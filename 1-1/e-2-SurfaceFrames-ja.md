[← Back](README-ja.md) | [English](e-2-SurfaceFrames.md) | [Japanese](e-2-SurfaceFrames-ja.md)

# 地上: 操作できてからのフレームを 1 つずつ

**主張.** [操作から城まで](f-5-PoleJoin-ja.md) は走り全体についての文 `model`、`hit`、`stop`、`box`、`off`、`next`、`startP`、`startV` を仮定していました。これらは定理になりました。残る仮定は 1 フレームについての文です。1〜8 フレーム目の縦の一歩（`vstep`）も本物の機械で定理になりました。そこで残るのは、スクロールの処理からあとが縦のバイトのうち 5 つを変えないことです。各フレームの始まりからプレイヤーのルーチンまでの部分は定理になりました。その部分の歩き（[`CtrlKeep`](#プレイヤーのルーチンまでのフレーム)）が、25 バイトを保ち、移動の要る状態でルーチンに来ることを示します。なのでフィールド `vBefore`、`Moves.at_ctrl`、`Moves.before`、`Moves.bits` はなくなりました。フレームの両端も、1 つの機械か 1 つのフレームの条件から定理になりました。数えるフレームはポーズでない状態で終わるので、プレイヤーのルーチンに来ます（`Moves.arrive` をなくし、新しく `unpaused`）。数えないフレームはプレイヤーのルーチンに来ないので、25 バイトを保ちます（`Moves.lag` をなくしました）。フレームの残り、プレイヤーのルーチンからフレームの終わりまでの歩き（[下](#フレーム全体-プレイヤーのルーチンから終わりまで)）が、ルーチンに来たフレームはポーズでない状態で終わることと、操作中のどのフレームもエリアの種類、泳ぎのフラグ、大きさの変化を保つことを示すようになりました。なので数えないフレームがルーチンに来ないことは定理です（`OnFrames.lagNo`。新しく `lagPaused`: 数えないフレームはポーズで終わる）。`state` の値のうち 3 つも定理です。各命令の新しい条件は `spare` です: 添字かポインタでの書き込みは、これらの 4 バイトを書きません。フレームは `Run` のフィールド `keep`（[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md)）のものと同じなので、フィールド `ends` もなくなりました。押している側がふさがれたフレームも定理になり、フィールド `masked` はなくなりました。`moves` の条件があと 2 つ定理になりました（[フレームの時間と位置の範囲](#フレームの時間と位置の範囲)）。移動のあいだにフレームが終わらないこと（`Moves.longer` をなくしました。移動の歩きと `CleanK` の条件 `time` から出ます）と、位置が範囲の端から遠いこと（`Moves.far` をなくしました。操作のときの位置と、`hstep` のとおりの前のフレームから出ます）です。`startP`、`startV` は本物の機械で証明しました。[地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md) の最後の段から出ます。条件はその切り替えの条件と、`left` が操作の前に 0 にならないことだけです。`moves` の部分があと 2 つ定理になりました。`state.prevA` はなくなりました: 操作中のどのフレームも、前のフレームの A と B の 7 ビット目を A と B の 7 ビット目と同じに保ちます（`OnFrames.prevAll`、[下](#前のフレームの-a-と-b)）。`After` のフィールド `md`、`rs` はなくなり、`stored` はスクロールの処理での機械の条件 `storedQ` になりました: フレームの終わりの動く向き、走りの速さ、覚えている速さは、スクロールの処理でのものです（`AfterKeep.keepH`、[下](#スクロールの処理からあと-3-つのバイト)）。各命令の新しい条件は `spareE` です: 添字かポインタでの書き込みは、これらの 5 バイトを書きません。`After` のフィールド `storedQ` もなくなりました: スクロールの処理での覚えている速さは、そこでの `|v|` です（`MovesAt.stored`、[下](#スクロールの処理での覚えている速さ)）。`ImposeFriction` がそれを書き、`FrameModel.stored_path` の歩きがスクロールの処理まで追います。フレームはプレイヤーのルーチンのあと、スクロールの処理に 1 度だけ来ます（`AfterKeep.subs_once`）。新しく `numbersCheck` の中の確認 `storedOK` と、`TopSpeed.frictionCheck`（`SurfaceRun.Statement` のフィールド `fric`）。フレーム `fr` はもう `Run` のデータではありません。`keep` の機械の上の定義です（`SurfaceFrames.frOf`、[下](#機械から読むフレーム)）。なのでフィールド `reads` はなくなりました。触る前の各フレームが、機械で始まり機械で終わる `TopSpeed.Frame` であることは、1 つのフレームか 1 つの機械の条件から証明です。新しく `state`（どのフレームでも。前は `Moves.state` で、`T` までの clean なフレームだけでした）、`coll`、`collide`、`farLate`。`collide` は `After` と同じフレームの部分の文なので、`After` は小さくなりました（`AfterR`）: サブ速さと、スクロールの処理で左へ動くか止まっているフレームは `collide` から出ます。この 4 つのうち 2 つはなくなりました。`coll` は定理です: プレイヤーのルーチンからのフレームの歩きで、`ImpedePlayerMove` で `X` を分けると、当たり判定のビットは 4 つの値のどれかのままです（`OnFrames.collAll`、[下](#当たり判定のビット)）。新しく `spareC`、各命令の条件です: 添字かポインタでの書き込みは当たり判定のビットを書きません。`farLate` はなくなりました: 操作から `farN` フレームより後に触る走りは別の場合で、その上限はフレームの数だけから出ます（`SurfaceLate`、[下](#遅く触る走り)）。そのために新しいのは `B.m` の確認だけです。`spareC` もなくなりました: `keep.cleanE` のガード `guardE` が当たり判定のビットも守ります（[下](#当たり判定のビット)）。`collide` の速さの部分も定理になりました: スクロールの処理からフレームの終わりまで速さを追う歩きが、終わりの速さはスクロールの処理のものか 0 だと示します（`OnFrames.collideAt`、[下](#スクロールの処理からあと-速さ)）。`collide` はいまは `CollideR` で、サブ速さと位置だけです。新しく `spareV`、各命令の条件です: 添字かポインタでの書き込みは速さを書きません。`spareV` もなくなりました: `guardE` が速さも守ります（`FrameKeep.speedE`）。`vAfter` の 10 のバイトのうち 4 つは定理になりました: 下向きの縦の力、ジャンプの始まりの高さ、ジャンプを止める値、A は、スクロールの処理からフレームの終わりまで変わりません（`OnFrames.kAt`、[下](#スクロールの処理からあと-縦の-4-つのバイト)）。`vAfter` は残りの 6 つを求めます。新しく、`guardE` がさらに 3 つのバイトを守ります（`FrameKeep.vertE`）。スクロールの処理からあとの向き、サブ速さ、当たり判定のビットは、小さい条件 2 つを残して定理になりました（[下](#スクロールの処理からあと-向きサブ速さ当たり判定のビット)）。歩きが示すのは、フレームがスクロールの処理から終わりまで向きとサブ速さを保つか、速さ 0 とサブ速さ 0 で終わることです（`FaceKeep.keepZ_end`）。`After` の残りと合わせると、速さ 0 で終わるフレームは当たりで、当たりには向きは要りません: `OneFrame` に `Hit` だけの場合が入りました。なので `After` の向きはもうフィールドではありません。ただし `J` より前のフレームは `hstep` のとおりでなければならないので、そこでは新しいフィールド `faceJ` が、速さ 0 とサブ速さ 0 で終わるフレームの向きを求めます。`collide` がサブ速さを求めるのも、そう終わるフレームだけです（`CollideS`）。もう 1 つの歩きは、スクロールの処理で右へ動くフレームが、当たり判定のビット `FF` か左をふさぐビットで終わるか、速さ 0 で終わることを示します（`FaceKeep.bits_end`）。なので `AfterR` は `AfterP` になりました: そこで右へ動くフレームの位置だけです。新しく、`guardE` がさらに 2 つのバイトを守ります（`FrameKeep.faceE`: 向きとサブ速さ）。`numbersCheck` の中の確認 `zCheck` と `bCheck` も新しいものです。縦の力も `vAfter` から外れました（[下](#スクロールの処理からあと-縦の力)）: 歩きが示すのは、フレームがスクロールの処理から終わりまで縦の力を保つか、ジャンプ台への着地が書く値を持って地面の上で終わることです（`FaceKeep.vf_end`）。縦のモデルは地面の上でその値を許します（`VStep`）。`vAfter` が求めるのは 5 つのバイトです。新しく、`guardE` がさらに 2 つのバイトを守ります（`FrameKeep.stateE`: プレイヤーの状態と縦の力）。`numbersCheck` の中の確認 `vfCheck` も新しいものです。

**第 24 回.** フィールド `collide` は、画面の左端より 1 px 左で始まる本物のフレームで偽でした（[フレームの始めの画面の左端](e-2-10-3-10-ScreenEdge-ja.md)）。その 3 番目の場合はいま P(b) ≤ base(M) + 256 を求めます。base(M) = max(P(M), edge(M)) で、edge(M) = 256·left(M) + 255 は端のピクセルの最後の位置です。`Hit`、`MaskStop`、`After` も同じことを言います。操作からのフレームは `wide` つきの `TopSpeed.Frame` で、その基点 B は base(seq (j − 1)) です（`frOf_B`）。新しいフィールドは 2 つです: 各フレームの `edge` と操作の始めの `edge₀`。これらで max(P, B) は 1 フレームに前と同じ上限しか増えません（`TopSpeed.Frame.posB`、`Frame.advB`、`SurfaceRun.chainB_reach`、`SurfaceRun.hit_boundB`）。だからルートの数は変わりません。`Surface` には新しい部分が 3 つあり、すべて証明済みです: `base`、`links`、`base₁`。その `hit` はいま、当たりより前のあるフレームでのモデルの位置を使います（`OnFrames.edge_behind`）。

**第 25 回.** フィールド `edge₀` は定理になりました（`edge_zero`、[操作の始めに画面の左端は彼の後ろ](e-2-10-3-11-EdgeStart-ja.md)）。`Start` は画面の左端の 2 つのバイトを持ち、それは横の土管からの切り替えの行から来ます。`numbersCheck` は、操作の始めの機械 `B.m` で端 ≤ P であることと、`B.m` が `m0` のプログラムを持つことを確かめます。`AreaRun` はそれを `edge₀ : 0 < g → edge(seq 0) ≤ P(seq 0)` として持ち、`Surface.base₁` は 1 ≤ g のときに求めます。

**第 26 回.** フィールド `edge` は定理になりました（`OnFrames.edgeAt`、[フレームの端の進み](e-2-10-3-13-EdgeStep-ja.md)）。端の 2 つのバイトをフレームの中で追う歩き、スクロールの規則、`collide`、`posW`、そしてスクロールの処理での 1 つの状態の新しいフィールド `near`（そこでスクロールが許されるとき left16(Q) + X(Q) + 2 ≤ pixel16(Q)）から出ます。`numbersCheck` は確認を 3 つ多く持ち（`EdgeStep.qCheck`、`EdgeStep.rCheck`、`ScrollRule.check`）、`FrameKeep.guardE` は端の 2 つのバイトを守ります（`FrameKeep.edgeE`）。

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
edge(m)           : 256·left(m) + 255     left(m): 画面の左端のピクセルとページ（SurfaceRead.edgeOf）
base(m)           : max(P(m), edge(m))                                                （SurfaceRead.baseOf）
Hit(i, a, b)      : v(b) ≤ 0 ∧ (P(b) ≤ P₂ − 256 ∨ P(b) ≤ base(a) + 256)
Coll(i, a, b)     : (P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = FF)
                  ∨ (0 < v₂ ∧ P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = noLeft)
                  ∨ Hit(i, a, b)
MaskStop(a, b)    : bits(a) = noLeft ∧ v(b) ≤ 0 ∧ P(b) ≤ base(a) + 256
OneFrame(i, a, b) : MaskStop(a, b) ∨ (Pre(i, a, b) ∧ Coll(i, a, b)) ∨ Hit(i, a, b)
```

当たりには `Pre` は要りません。速さ 0 で終わるフレームの向きは、`hstep` の向きと違うことがあります: 画面の左端の近くのよじ登れるタイルが向きを変えます。当たりで走りはモデルを離れます（`step_of_one : Clean(a) ∧ OneFrame(i, a, b) → (Follow(i, a, b) ∧ Clean(b)) ∨ Hit(i, a, b)`。文は前と同じです）。

`Follow(i, a, b)` は [地下の部屋](c-5-RoomJoin-ja.md) の `RoomJoin.Follow` と同じ形です。`fr.hs n = hs(seq n)`、`fr.P n = P(seq n)` です。数えるフレーム `j` の入力は `inp(j) = inAt(fm j, pad j, arr j)` です。`arr j` はフレームが初めてプレイヤーのルーチンにいる命令です（次の節）。前はフレームの両端から読む `readIn(a, b)` で、フィールド `input` が 2 つは同じと言っていました。今はルーチンが読む入力そのものなので、そのフィールドはなくなりました。

## 本物の機械の 1 フレーム

[`FrameModel.move_model`](../0-0/0-3-2-FrameModel-ja.md) は本物のフレームの移動を証明しています。プレイヤーのルーチンからスクロールの処理まで、`hs` は `hstep` のとおりで、`P` は `16·v₂` 動きます。なので `OneFrame` は、フレームの移動の外の部分から出る定理です。

`fm j` は数えるフレーム `j` が始まるときの機械です。`seq (j − 1)` か、そのあとの `lag` のフレームのあとです。`pad j` はその入力です。どちらも `Run` のフィールド `keep`（`FrameKeep.Frames`）のものです。`arr j = arrAt(fm j, pad j)` はフレームが初めてプレイヤーのルーチンにいる命令の番号です（`CtrlKeep.arrAt`: `pc(trM(n)) = PlayerCtrlRoutine` となる最初の `n ≤ fuelPerFrame`。前は `OnFrames` のデータでしたが、今は定義です）。`R` はそこでの機械、`Q` はスクロールの処理に来たときの機械です。`b = frame(M, i)` はフレームの終わりの機械です。

```
Masked(i, a)       : bits(a) & lr ≠ lr            lr は hstep が i から読む左右

After(a, Q, b)     : b の f は Q のもの ∧ (b の fd は Q のもの ∨ (v(b) = 0 ∧ f(b) = 0))
                     ∧ ( (P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = FF)
                       ∨ (0 < v(Q) ∧ P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = noLeft)
                       ∨ (v(b) ≤ 0 ∧ (P(b) ≤ P(Q) − 256 ∨ P(b) ≤ base(a) + 256)) )
AfterP(a, Q, b)    : 0 < v(Q)  →  (v(b) = v(Q) → P(b) = P(Q))                          After がまだ求めるもの: 位置。keep は定理 OnFrames.keepAt、stop は Moves.stop
                                  ∧ (v(b) = 0 → P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256)
After.of           : AfterP(a, Q, b) ∧ CollideE(a, Q, b) ∧ (fd(b) = fd(Q) ∨ (v(b) = 0 ∧ f(b) = 0)) ∧ (0 < v(Q) → bits(b) ∈ {FF, noLeft} ∨ v(b) = 0)
                     ∧ P(Q) = P(a) + 16·v(Q)  →  After(a, Q, b)
hit_of_stop        : After(a, Q, b) ∧ v(b) = 0 ∧ v₂ = v(Q) ∧ P(Q) = P(a) + 16·v(Q)  →  Hit(i, a, b)
AfterK(a, Q, b)    : After(a, Q, b) ∧ b の md, RunningSpeed, abs は Q のもの          3 つのバイトは定理（AfterKeep.keepH）
                     ∧ abs(Q) = |v(Q)|                                              定理（MovesAt.stored）

MovesAt(a, M, x, n₀) : AtCtrl0(R)                                  プレイヤーのルーチンでの状態。FrameModel が要るもの（ふさぎは除く）
                       ∧ R の横の 8 バイトは a のもの                  a から R まで書かれない
                       ∧ bits(R) = bits(a)                             当たり判定のビットも書かれない
                       ∧ frame(R) = frame(M)                           ルーチンは M のフレームの中で来る（Arrive）
                       ∧ ∀ n, pc(trM(n)) ≠ idle → fdot(trM(n)) ≤ dotsPerFrame − 64     CleanK の条件 time
                       ∧ idleAt(idle) ∧ far(a) ∧ after ∧ collide       アイドルループは自分への JMP。far は下。各 Q で AfterP と CollideE
                       ∧ face                                          各 Q で fd(b) = fd(Q) ∨ (v(b) = 0 ∧ f(b) = 0)（FaceKeep.keepZ_end）
                       ∧ bitsR                                         各 Q で 0 < v(Q) → bits(b) ∈ {FF, noLeft} ∨ v(b) = 0（FaceKeep.bits_end）
                       ∧ keepH                                         フレームの終わりの md, RunningSpeed, abs は各 Q のもの（AfterKeep.keepH）
                       ∧ stored                                        各 Q で abs(Q) = |v(Q)|（storedQ_of）

CtlState(a)        : Player_State(a) ∈ {0, 1, 2} ∧ JumpspringAnimCtrl(a) = 0
PrevOK(a)          : PrevA(a) & 80 = A_B(a) & 80                                         どのフレームでも定理（OnFrames.prevAll）
AreaOK(v, a)       : AreaType(a) = v ∧ SwimmingFlag(a) = 0 ∧ PlayerChangeSizeFlag(a) = 0      どのフレームでも定理（OnFrames.areaAll）
AreaRun(v)         : v = AreaType(B.m) ∈ {1, 2, 3} ∧ afterCheck(v) ∧ hCheck(v) ∧ ∀ n < ix g, AreaOK(v, all n)

Arrive(M, x, n₀)   : pc(trM(n₀)) = PlayerCtrlRoutine で M のフレームの中、n₀ より前の命令はそこにない

Moves(a, M, x, n₀) : stop     スクロールの処理に来るどの Q でも 0 < v(Q) ∧ v(b) = 0 → P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256     （AfterP.stop。state はいまは OnFrames のフィールド state）
far(a)             : 2048 ≤ P(a) ∧ P(a) + 2048 < 2²⁴

Moves.toAt    : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Clean(a) ∧ Arrive(M, x, n₀) ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ AreaOK(v, a) ∧ v ∈ {1, 2, 3}
                ∧ far(a) ∧ idleAt(idle) ∧ keepH ∧ once ∧ modelOK ∧ frictionCheck ∧ storedOK ∧ CtlState(a) ∧ keep ∧ Moves  →  MovesAt      keep は各 Q で AfterP.keep（OnFrames.keepAt）
at_subs       : modelOK ∧ MovesAt ∧ ¬Masked  →  スクロールの処理に来る Q があって hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∧ P(Q) = P(a) + 16·v(Q) ∧ AfterK(a, Q, b)
one_of_moves  : modelOK ∧ MovesAt ∧ ¬Masked  →  (Pre(inAt(M, x, n₀), a, b) ∧ Coll(inAt(M, x, n₀), a, b)) ∨ Hit(inAt(M, x, n₀), a, b)
at_subsM      : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  スクロールの処理に来る Q があって (hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∨ v(Q) = 0)
                                                                  ∧ P(Q) = P(a) + 16·v(Q) ∧ AfterK(a, Q, b)
one_of_movesM : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  OneFrame(inAt(M, x, n₀), a, b)
one_of_frames : OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaRun(v) ∧ Clean(seq (j − 1)) ∧ far(seq (j − 1)) ∧ idleAt(idle)  →  OneFrame(inp j, seq (j − 1), seq j)
```

`one_of_moves` は、フレームの終わりの向きがスクロールの処理のものなら `Pre` を出し（`pre_of_after`）、フレームが速さ 0 で終わるなら当たりを出します（`hit_of_stop`）。`face` と `bitsR` は `OnFrames.movesAt` の中で `FaceKeep` の歩きから出ます。`bitsR` は、clean な状態の当たり判定のビットが `FF` か左をふさぐビットであることを使います。

`keepA` と `StartK`、`CleanK`、`ctrlCheck` は次の節にあります。`all n` は `keep` のフレームで、数えるものも数えないものも入ります。`ix g` は触るフレームです。`StartK(all n)` は操作できるときの機械から出る定理 `FrameKeep.Frames.all_start` です。各命令の `CleanK` はフィールド `keep.clean` です。`Moves.toAt` のほかの条件は定理です（`OnFrames.arrive`、`OnFrames.lagKeep`、次の節。`keepH` は `OnFrames.movesAt` の中で `AfterKeep.keepH` から、`once` は `AfterKeep.subs_once` から）。

`idle` はアイドルループ（`EndlessLoop`）で、`idleAt(idle)` はそれが自分への `JMP` だと言います。`numbersCheck` の中の ROM の確認です。`modelOK` は `FrameModel` の ROM の確認です。これは `numbersCheck` の一部になったので、非公開の証明が `native_decide` で計算します（約 3 秒増えます）。`move_model` は押している側がふさがれていないことを要ります。`bits(R) = bits(a)` があれば、これは `¬Masked` です。

**ふさがれたフレーム.** 押している側がふさがれたフレーム（`Masked`）では、摩擦の処理がふさぎを読み、`hstep` は読みません。[`FrameModel.move_masked`](../0-0/0-3-2-FrameModel-ja.md) は、それでもフレームが `hstep` のとおりになるか、速さを 0 にすることを証明します。押している側がふさがれた Clean な状態は、左をふさぐビットを持ち、右へ動いています（`masked_clean`）。スクロールの処理で速さが 0 なら、`After` から `MaskStop` が出ます。`maskOK` は `move_masked` の ROM の確認で（約 0.1 秒）、`numbersCheck` の一部です。

仮定のフィールドです（`OnFrames`）。全部 `Run` の `frames` に入ります。`fm`、`pad` は `keep` のものです。

```
state    : 1 ≤ j ≤ g   →  CtlState(seq (j − 1))                       （前は Moves.state で、T までの clean なフレームだけ）
collide  : 1 ≤ j < g、Q はスクロールの処理  →  CollideS(seq (j − 1), Q, seq j, Calls)  Calls: Q からフレームの中で押し戻しか補正の入口に来る
           CollideS(M, Q, b, c) : (v(b) = 0 ∧ f(b) = 0 → f(Q) = 0) ∧ (c → ¬(0 < v(Q) ∧ v(b) = v(Q)) → P(b) = P(Q) ∨ P(b) = P(Q) − 256 ∨ (P(Q) ≤ P(b) ≤ base(M) + 256 ∧ v(Q) ≤ 0))
                                                  速さと、ほとんどのフレームのサブ速さは定理（OnFrames.collideAt）。右への速さを保つフレームと呼び出しのないフレームの位置も（OnFrames.keepAt、OnFrames.stillAt）
near     : 1 ≤ j < g → arrAt ≤ k → pc(Q) = PlayerSubs → Near(Q)、Q = trace(fm j, pad j, k)        （第 26 回。第 24 回のフィールド edge のかわり:
           Near(Q) := Allows(Q) → left16(Q) + X(Q) + 2 ≤ pixel16(Q)）
moves    : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1))  →  Moves(seq (j − 1), fm j, pad j, arr j)     Moves は AfterP.stop だけになった
posW     : 1 ≤ j < g、Q はスクロールの処理、R は Q からフレームの終わりまでの命令  →  PosW(R)       位置を番地で書くのは押し戻しと補正の内側だけ。その外で添字かポインタで書く命令は位置を書かない
           （第 23 回: 絶対番地と添字で書き、基の番地からどの添字でも位置に届かない命令には求めない: PositionKeep.absFar）
clampR   : 1 ≤ j < g、Q はスクロールの処理、0 < v(Q)、v(seq j) = v(Q)、R は Q からフレームの終わりまでの命令  →  ClampR(R)     R が補正の入口で 0 < v(R) なら、補正先は P(R)
           （第 23 回: 右への速さを保つフレームだけで求める。keep_frame が使うのはそこだけ）
vAfter   : 1 ≤ j < J, j < g、Q はスクロールの処理  →  seq j での vHard の 5 つのバイトは Q のもの
           vHard = y, mf, vy, dummy, st              （vfd、origin、DTHJ と A は定理 OnFrames.kAt。vf は定理 OnFrames.vfAt）
faceJ    : 1 ≤ j < J, j < g, Q はスクロールの処理, v(seq j) = 0, f(seq j) = 0  →  fd(seq j) = fd(Q)
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
vBefore    : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Arrive ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ PrevOK(a)  →  R での縦のバイトと A は a のもの、
               かつ PrevA(R) & 80 = A_B(R) & 80                        （前のフィールド vBefore）
VStep(a, b) : vs(b) = vNext(a, b) ∨ (st(vNext(a, b)) = 0 ∧ vs(b) = vNext(a, b) で vf := cv)          cv = FaceKeep.vfC、ジャンプ台への着地が書く値
vert_of    : vertOK ∧ ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ far(seq (j − 1)) ∧ idleAt(idle) ∧ HaltOK(seq (j − 1)) ∧ PrevOK(seq (j − 1))
               →  VStep(seq (j − 1), seq j) ∧ HaltOK(seq j)
```

操作できるときの状態はジャンプ中ではないので（`numbersCheck` の中）、`HaltOK(seq 0)` が成り立ちます。`PrevOK(seq (j − 1))` は `OnFrames.prevAll` から出ます。なので `quiet_upto` は、ほかの事実といっしょに、`j < J` のすべてで `VStep(seq (j − 1), seq j)` と `HaltOK(seq j)` を帰納法で証明します。`vertOK` は `numbersCheck` の一部です（約 0.1 秒増えます）。

| 前のフィールド | 今 |
|---|---|
| `step`: Clean なフレームは全部 `OneFrame` | `moves`（移動の外の部分）、`ends` |
| `masked`: 押している側がふさがれたフレームは `OneFrame` | 定理 `one_of_movesM`（`moves` と `FrameModel.move_masked` から）。新しく `Moves.bits`。`Moves.at_ctrl` は `AtCtrl0` で、ふさぎの条件はない |
| `reads`: `v₂(fr j) = v₂` | なくなった。`box` が本物の機械 `Q` と `seq j` の文なので、フレームの `v₂` は要らない |
| `reads`: フレーム `fr`（`Run` のデータ）は `seq` のバイトで始まり終わる | なくなった。`fr` は機械の上の定義 `frOf` で、`OnFrames.reads` が証明する。新しく `state`（どのフレームでも）、`coll`、`collide`、`farLate`（[下](#機械から読むフレーム)） |
| `coll`: 触る前の各フレームの終わりで、当たり判定のビットは `collBits` の 4 つの値のどれか | 定理 `OnFrames.collAll`。`ImpedePlayerMove` で `X` を分ける `CollKeep` の歩きと、操作のときからの `keep` のフレームについての帰納法から。新しく `spareC`、`numbersCheck` の中の確認 `collCheck` と `collBitsOK`（[下](#当たり判定のビット)） |
| `farLate`: 操作から 746 フレーム目以降で、位置は範囲の両端から 8 ピクセル以上離れている | なくなった。フレームを読む定理は `g ≤ farN(B.m)` を求める。それより後に触る走りは、フレームの数で上限が出る（`SurfaceLate.level_ge_of_late`）。`route_1_1` が 2 つの場合に分ける。新しく確認 `pole_far_count`（`492 ≤ farN(B.m)`）（[下](#遅く触る走り)） |
| `Moves.state`: 前のフレームの終わりで `CtlState`。`T` までの clean なフレームだけ | `OnFrames` のフィールド `state`。触るまでのどのフレームでも。`frOf` がどのフレームでも要る |
| `After.f` と、`v(Q) ≤ 0` のときの `After.coll` | 定理 `After.of`。`collide` と移動から。`Moves.after` は `AfterR` になった: 向きと、`v(Q) > 0` のときの `coll`（いまは `AfterP`。下の行） |
| `fr j` についての `box` | 本物の機械についての `box`、スクロールの処理から |
| `Moves.input`: ルーチンは `readIn(a, b)` を読む | なくなった。モデルの入力はルーチンが読むものそのもの |
| `vert`: 1〜8 フレーム目は `vstep` のとおり | 定理 `vert_of`。新しく `vBefore`、`vAfter`（移動のルーチンの外は縦のバイトを変えない） |
| `vBefore`: プレイヤーのルーチンまで縦のバイトと A は前のフレームのもので、PrevA は A | 定理 `vBefore`（前の名前は `Moves.vBefore`）。`CtrlKeep` の歩きから。`OnFrames.lagKeep` と前のフレームの `PrevOK`（`OnFrames.prevAll`）を使う |
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
| `CtlState.prevA`: 前のフレームの終わりで、前のフレームの A の 7 ビット目は A のもの | 定理 `OnFrames.prevAll`。`noStore` の書き込みで道を切った切れ目からの歩き（`PrevKeep.prev_end`）と、操作のときからの帰納法から。新しく `spareE`（その 2 バイト）、`Start.ab`、`Start.prev`（段から）、`numbersCheck` の中の確認 `prevCheck` と `PrevOK(B.m)` |
| `After.md`、`After.rs`、`After.stored`: フレームの終わりの動く向き、走りの速さが 0 か、覚えている速さ | 定理 `AfterKeep.keepH`: フレームの終わりの 3 バイトはスクロールの処理でのもの。`stored` は `storedQ`（スクロールの処理の機械で abs(Q) = v(Q) の絶対値）になった。新しく `spareE`（その 3 バイト）、`numbersCheck` の中の確認 `hCheck` |
| `spareC`: 触る前の各フレームの各命令は、添字かポインタで当たり判定のビットを書かない | `keep.cleanE` の一部。`FrameKeep.guardE` が当たり判定のビットも守る（`FrameKeep.collE`）。`coll_end` は `cleanE` だけを求める（[下](#当たり判定のビット)） |
| `collide` の速さの部分（`CollideE.v`）: 速さはスクロールの処理のものか 0 | 定理 `OnFrames.collideAt`（`CollideKeep.speed_end`）。`collide` は `CollideR`（サブ速さと位置）になった（いまは `CollideS`。下の行）。新しく `spareV`、`numbersCheck` の中の確認 `vCheck`（[下](#スクロールの処理からあと-速さ)） |
| `spareV`: 触る前のフレームのどの命令も、添字かポインタで速さを書かない | `keep.cleanE` の一部: `FrameKeep.guardE` が速さも守る（`FrameKeep.speedE`）。`speed_end` は `cleanE` だけを求める（[下](#スクロールの処理からあと-速さ)） |
| `vAfter`: スクロールの処理からあと、縦の 10 のバイト（`vKeep` と A）は変わらない | 4 つは定理 `OnFrames.kAt`（`VertKeep.keep_end`）: 下向きの縦の力、ジャンプの始まりの高さ、ジャンプを止める値、A。`vAfter` は `vHard` の 6 つを求める。新しく `guardE` の `FrameKeep.vertE`（3 つのバイト）、`numbersCheck` の中の確認 `kCheck`（[下](#スクロールの処理からあと-縦の-4-つのバイト)） |
| `vAfter` のうち縦の力 | 定理 `OnFrames.vfAt`（`FaceKeep.vf_end`）: 縦の力は変わらないか、フレームはジャンプ台への着地の値を持って地面の上で終わる。`vert_of` は `VStep` を出し、`vCheck` は地面の上で両方の値を追う。`vAfter` が求めるのは 5 つのバイト。新しく `guardE` の `FrameKeep.stateE`（2 バイト）、`numbersCheck` の中の確認 `vfCheck`（[下](#スクロールの処理からあと-縦の力)） |
| `AfterR.fd`: `T` までの clean な状態からのフレームの終わりの向きは、スクロールの処理のもの | 定理 `FaceKeep.keepZ_end`（向きは変わらないか、フレームは速さ 0 とサブ速さ 0 で終わる）と、`Hit` だけの場合を持つ `OneFrame`（`hit_of_stop`）。新しく `faceJ`（`J` より前で、速さ 0 とサブ速さ 0 で終わるフレーム）、`guardE` の中の `FrameKeep.faceE`（2 バイト）、`numbersCheck` の中の確認 `zCheck`（[下](#スクロールの処理からあと-向きサブ速さ当たり判定のビット)） |
| `AfterR.coll`: スクロールの処理で右へ動くフレームは、何もしないか、左をふさぐか、当たり | 当たり判定のビットは定理 `FaceKeep.bits_end`、速さは `CollideKeep.speed_end`。`Moves.after` はいまは `AfterP`: 位置。新しく `numbersCheck` の中の確認 `bCheck` |
| `AfterP.keep`: スクロールの処理で右へ動き、その速さで終わるフレームは位置を保つ。`collide` の位置もそのフレームと、呼び出しのないフレームで | 定理 `OnFrames.keepAt`（`PositionKeep.keep_frame`）と `OnFrames.stillAt`（`PositionKeep.still_frame`）。`Moves` は `stop` だけ。`collide` はそのフレームの位置を求めない（新しい引数 `Calls`）。新しく 1 命令ずつのフィールド `posW`、`clampR`、`numbersCheck` の中の確認 `pCheck`（[位置を保つフレーム](e-2-10-3-8-PositionKeep-ja.md)） |
| すべてのフレームの `clampR`（第 23 回） | スクロールの処理で右へ動き、その速さで終わるフレームだけで求める。`PositionKeep.keep_frame` が使うのはそこだけ。フィールド `collide` は本物のフレームで偽（画面の左端より 1 px 左で始まるフレーム）: [フレームの始めの画面の左端](e-2-10-3-10-ScreenEdge-ja.md) |
| `collide` の 3 番目の場合 P(b) ≤ P(M) + 256（本物のフレームで偽、第 23 回） | 第 24 回: 画面の左端を入れた P(b) ≤ base(M) + 256。新しい: フィールド `edge`（1 フレーム）と `edge₀`（操作の始めの状態） |
| `edge`: 1 ≤ j < g → edge(seq j) ≤ max(base(seq (j − 1)), P(seq j))（第 24 回） | 第 26 回: `EdgeStep` の歩き、スクロールの規則、`collide`、`posW` からの定理 `OnFrames.edgeAt`。新しいフィールドはスクロールの処理での `near`。`guardE` は端の 2 つのバイトを守る（[フレームの端の進み](e-2-10-3-13-EdgeStep-ja.md)） |
| `edge₀`: 操作の始めに edge(seq 0) ≤ P(seq 0)（第 24 回） | 第 25 回: 横の土管からの切り替えの行（`Start.edgeX`、`Start.edgeP`）と `numbersCheck`（`Numbers.edgeB`）からの定理 `edge_zero`。`AreaRun.edge₀` の中（[操作の始めに画面の左端は彼の後ろ](e-2-10-3-11-EdgeStart-ja.md)）。`Surface.base₁` は 1 ≤ g のときに求める。新しいフィールドはない |
| `collide` のサブ速さの部分（`CollideR.f`）: サブ速さは変わらない | 速さ 0 とサブ速さ 0 で終わるフレームのほかは定理 `FaceKeep.keepZ_end`。`collide` はいまは `CollideS`: 位置と、そう終わるフレームのサブ速さ |
| `After.storedQ`: スクロールの処理での覚えている速さはそこでの `\|v\|` | 定理 `storedQ_of`: `FrameModel.stored_path` の歩きと `AfterKeep.subs_once`。新しく `numbersCheck` の中の確認 `storedOK` と、`TopSpeed.frictionCheck`（`SurfaceRun.Statement` のフィールド `fric`） |

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

## 前のフレームの A と B

プレイヤーのルーチンは A と B（`A_B_Buttons`）をパッドのビットから書き、ゲームエンジンは終わりにそれを前のフレームの A と B（`PreviousA_B_Buttons`）に写します（ルーチン `SaveAB`）。`PrevKeep` は、操作中のフレームが 2 つの 7 ビット目を同じに保つことを示します。

```
PrevOK(m)        : PrevA(m) & 80 = A_B(m) & 80
SpareAB(m)       : m の添字かポインタでの書き込みは、行き先 t < 2000h のとき、A_B も PrevA も書かない
CtlStore(m)      : m の命令は、ルーチン、モード、タスクを番地で書く
prev_end         : ctrlCheck ∧ prevCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_F(trM(n)) ∧ SpareAB(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ PrevOK(M)
                   →  PrevOK(frame(M, x))
OnFrames.prevAll : ctrlCheck ∧ prevCheck(v) ∧ AreaRun(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ PrevOK(seq 0)  →  ∀ n < ix g, PrevOK(all n)
```

`CleanK_F` は `FrameKeep.guardF` の `CleanK` です（フィールド `keep.cleanF`）。触るフレームより前のフレームに `CtlStore` の命令はありません（フィールド `keep.noStore`）。

* **歩き.** ポーズのビットの歩きはプレイヤーのルーチン（切れ目）に来ます。そこから、パッドのビットの 7 ビット目の値 `b` ごとに、`FrameKeep.walkKC` の歩きがフレームの終わりまで追います。A_B と PrevA も守り、ルーチン、モード、タスクを番地で書く命令で道を止めます。フレームの終わりで A_B と PrevA の 7 ビット目が `b` であることを確かめます。ルーチンに来ないフレームは両方のバイトを保ちます（`CtrlKeep.keep_of_noCut`）。
* **切る理由.** 第 8 回の、切らない探索は 26 のフレームの終わりで失敗しました。そこでは PrevA が分かりませんでした。失敗する道は、タスクを番地で書く道です: 斧（`HandleAxeMetatile`）とエリアの切り替え（`ChgAreaMode`）。タスクがゲームコアのものより小さいと、ゲームコアはゲームエンジンの前に戻るので、`SaveAB` は動きません。ルーチン、モード、タスクへの書き込み（8 か所: この 2 つとルーチンへの 6 つ）で道を切ると、探索の失敗は 0、表は 7,079 状態です（前は 74,910）。
* **帰納法.** `seq 0` は `B.m` の A_B と PrevA を持ちます（`Start`、切り替えの段から。段は PrevA も知っています）。`numbersCheck` は `PrevOK(B.m)` を確かめます。触るフレームより前の `keep` の各フレームは `PrevOK` を保ちます。
* **数.** `prevCheck`: 切れ目までのポーズのビットの歩きと、そこからの 2 つの歩き。ネイティブで 3.1 秒。`numbersCheck` の一部です（`Numbers.prev`）。

## スクロールの処理からあと: 3 つのバイト

`AfterKeep` はプレイヤーのルーチンからのフレームを 2 つの歩きで追います。1 つ目は切れ目から、フレームが初めてスクロールの処理（`PlayerSubs`）に来るところまでです。2 つ目はそこからフレームの終わりまでで、1 つのバイトを `TaintRun` のカウンタとして追います（`Env.rkI`）: そのバイトへのどの書き込みでも失敗し、フレームの終わりでまだ追えていることを確かめます。フレームがまたスクロールの処理に来ても失敗します。どちらもルーチン、モード、タスクを番地で書く命令で道を止めます。

```
hI          = Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute
SpareH(m)   : m の添字かポインタでの書き込みは、行き先 t < 2000h のとき、hI のバイトを書かない
keepH       : ctrlCheck ∧ hCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_F(trM(n)) ∧ SpareH(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
              →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ hI, y(frame(M, x)) = y(trM(k))
SpareE(m)   : SpareAB(m) ∧ SpareH(m)          前のフィールド spareE。いまは keep.cleanE の一部（GuardE）
```

* **数.** 1 つ目の歩き: 1,769 歩、表は 134 状態、スクロールの処理で 8 状態。2 つ目の歩き: バイトごとに 61,977 歩、表は 3,986 状態、失敗 0。`hCheck`: ネイティブで 1.9 秒。`numbersCheck` の一部です（`Numbers.keepH`）。
* **追うバイトのある 1 歩.** `FrameKeep.s_kstep` はカウンタが 2 以上であることを要ります。2 つ目の歩きは代わりに、追うバイトを減らす命令がないこと（`isRkDec`）を確かめます。`LagFrames` と同じです: `s_kstepL`。

**歩きが出会う書き込み.** プログラム `after-bytes` は、横のバイトのそれぞれについて、スクロールの処理の 8 状態から 2 つ目の探索を動かします。

* `keep.cleanF` だけで、バイトを守らないと、歩きはそれぞれのバイトを、行き先の分からない添字かポインタでの書き込み約 95 か所で失います: 敵、スプライト、エリアの読み取り。`guardK` が守る `SprObject_X_MoveForce` はそこでは失いません。
* バイトも守ると、`hI` の 3 バイトは閉じます。ほかは番地での書き込みに出会います:

| バイト | 歩きが出会う、スクロールの処理からあとの書き込み |
|---|---|
| 速さ | `KillPlayer`、`KeepOnscr`（画面の端）、`ImpedePlayerMove`、`PutPlayerOnVine` |
| サブ速さ | `PutPlayerOnVine` |
| 向き | `FlagpoleCollision`、`PutPlayerOnVine` |
| x | 添字 0 の移動のルーチン（歩きは分からない添字を分ける）、`PositionPlayerOnHPlat`、`ImpedePlayerMove`、`KeepOnscr`、`PutPlayerOnVine` |
| ページ | x の書き込みと、`ExecGameLoopback` |
| 端数 | 添字 0 の移動のルーチン |
| 当たり判定のビット | `ImpedePlayerMove`、`PlayerBGCollision` の始め |

`KillPlayer` はルーチンを書く前に速さを書くので、ルーチンへの書き込みで切っても、その前に出会います。`PutPlayerOnVine` には、ルーチンを書かない道からも来ます（ステータスバーより下のつたのタイル）。なのでサブ速さと向きは `After` に残ります: 歩きは、つたにもポールにも触らないことを知る必要があり、それは地図です。

## スクロールの処理からあと: 速さ

`collide` の速さの部分 `CollideE.v`（終わりの速さはスクロールの処理のものか 0）は、いまは歩きから出る定理です（`Theorems/CollideKeep.lean`）。1 つ目の歩きは `AfterKeep` のもので、切れ目からスクロールの処理まで行きます。2 つ目の歩きはそこからフレームの終わりまで、速さを `TaintRun` のカウンタとして追います（`Env.rkI`）。`AfterKeep` の 2 つ目の歩きと違うのは 2 つです。速さを番地で書く命令の前で、歩きは速さを追うのをやめます（`rkOff`）。フレームの終わりでは、速さをまだ追えているか、速さが 0 と分かっていることを求めます（`finV`）。

```
SpareV(m)          : m の添字かポインタでの書き込みは、行き先 t < 2000h のとき、速さを書かない      （CleanK_E の一部: spareV_of）
rkOff(A)           : A が速さを追っていて、A.pc の命令が速さを番地で書くなら、追うのをやめた A。そうでなければ A
finV(B)            : B は速さをまだ追っている ∨ B で速さは 0 と分かっている
speed_end          : ctrlCheck ∧ vCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
                     →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  v(frame(M, x)) = v(trM(k)) ∨ v(frame(M, x)) = 0
CollideR(M, Q, b)  : f(b) = f(Q) ∧ (P(b) = P(Q) ∨ P(b) = P(Q) − 256 ∨ (P(Q) ≤ P(b) ≤ base(M) + 256 ∧ v(Q) ≤ 0))        前のフィールド collide。いまは CollideS とサブ速さの歩きから（CollideS.toR）
CollideR.toE       : CollideR(B₀, Q, b) ∧ (v(b) = v(Q) ∨ v(b) = 0)  →  CollideE(B₀, Q, b)
OnFrames.collideAt : 1 ≤ j < g ∧ k ≥ arr j ∧ pc(trM(k)) = PlayerSubs  →  CollideE(base(seq (j − 1)), trM(k), frame(fm j, pad j))       M = fm j, x = pad j
```

* **かけら.** 追うのをやめた状態は、もとの状態が覆う機械をどれも覆います（`cov_rkOff`）: `Sim` の `rkv` は追っているときだけ求めます。歩き `walkKV` は `AfterKeep.walkKR` に、`FrameKeep.preK` のかけらのあとで `rkOff` のかけらを足したものです（`CollKeep.walkKX` と同じ形）。`endKV` は `AfterKeep.endKR` と同じ証明です。
* **数.** 2 つ目の歩き: スクロールの処理の 8 状態から 123,279 歩、表は 7,888 状態、失敗 0。速さを追うのをやめるのは 4 か所です: 画面の端（`KeepOnscr`）、当たり判定（`ImpedePlayerMove`）、よじ登り（`PutPlayerOnVine`）の 0 の書き込みと、やられ（`KillPlayer`）。やられの道はそのあとルーチンを書くので、`noStore` で切れます。`vCheck` はプログラムで 1.5 秒です。`numbersCheck` の一部なので（`Numbers.vkeep`、`AreaRun.vkeep`）、`pole_numbers` は約 1.5 秒長くなります。
* **守るバイト.** 速さを守らないと、歩きは速さを、行き先の分からない添字かポインタでの書き込み約 95 か所で失います（`after-bytes guard`）。なので速さを守る必要があります。`FrameKeep.guardE` が速さを守る（`FrameKeep.speedE`）ので、`CleanK_E` から歩きのガードの `CleanK` が出ます（`cleanV_of`）。前の 1 命令の条件 `spareV` は `CleanK_E` の一部です（`spareV_of`。プレイヤー自身の端数の書き込みは除きます。`CleanK` はそれを求めません）。プレイヤーの状態の守りやフレームの終わりの状態の条件は要りません。
* **速さを `guardE` に入れて測ったもの.** `keep-frames-check FM2 100`（地上の 224,813 フレーム。触るフレームとポーズのあるフレームも含む）: 守るバイトへの添字かポインタでの書き込みはありません。`open-real-check FM2 300`（オープニングのフレーム。パート a の `Real.cleanK` も `CleanK_E` を求めます）: 条件を満たさないフレームは 0。`phase-frame-check`（`PhaseFrame` の歩きは `guardE` に 2 つのバイトを足したもの）: 確認は真です。`open-air-search all`: 失敗 0、表は前と同じ 95,459 の状態。はじめの 3 つは `vertE` の 3 つのバイトも守って（下）もう一度走らせました: 同じ数で、失敗 0 です。

**サブ速さ.** 次の節にあります: 終わりで「まだ追っている、または速さとサブ速さが 0 と分かっている」を求める歩きは閉じます。終わりで「まだ追っている、またはプレイヤーの状態が 0、1、2 でないと分かっている」を求めると閉じません: 141,003 歩、表は 10,650 状態、失敗 1 です（`collide-keep-check`）。失敗の道は次のとおりです: 横の判定がよじ登りのルーチン（`PutPlayerOnVine`）に来て、サブ速さを 0、状態を 3 にします。同じフレームのあとで、台の当たり判定（`SetCollisionFlag`）が状態を 0 にします。なのでフレームの終わりの状態の条件（`state`）ではこの道を除けません。歩きは地図も物も知りません。

**位置（測っただけで、証明していない）.** `CollideS` と `AfterP` が位置を求めます。スクロールの処理からあとで、位置の 3 バイトは次の場所で書かれます（`after-bytes prot`: そのバイトを守った歩き）:

| 場所 | 書くもの | 歩きが閉じない理由 |
|---|---|---|
| スクロールの処理の端の止め（`KeepOnscr`） | ピクセルとページ: 画面の端。端から離れる向きのボタンを押していなければ速さを 0 にする | `P(b) ≤ P(a) + 256` かどうかは、端の位置とフレームの始まりの位置によります。歩きが知らない 2 つの値の関係です |
| 当たり判定のルーチンの押し（`ImpedePlayerMove`） | 左か右へ 1 ピクセル（ページへの繰り上がりつき）と、速さ 0 | 歩きが知るのはバイトで、和ではありません。`P(b) = P(Q) − 256` は前後の 3 バイトの関係です。そのルーチンの本物の機械での補題と、そこで歩きを切ることが要ります |
| よじ登りのルーチン（`PutPlayerOnVine`） | タイルの列からのピクセルと、ページ | 地図 |
| 横に動く台（`PositionPlayerOnHPlat`） | 台の位置からのピクセルとページ | 物 |
| 添字つきの移動のルーチン（`MoveObjectHorizontally`） | その添字の物の端数、ピクセル、ページ | スクロールの処理からあとの添字は敵のもので 1 以上ですが、歩きは物の番号（`ObjectOffset`）を知りません。表が忘れます。ピクセルとページは `guardE` に入れられません: スクロールの処理の前に、プレイヤー自身の移動が添字 0 で書きます。`CleanK` が除くのは端数の書き込みだけです |
| 城のループ（`ExecGameLoopback`） | ページ | ほかの面の道 |

なので位置は仮定のままです。本物のフレーム（`pos-after-real`、[下](#スクロールの処理からあと-向きサブ速さ当たり判定のビット)）で位置を書くのは、はじめの 2 つの場所だけです。

**本物のフレームで測ったもの.** `collide-real FM2 200`（走りはルーチン、モード、タスクを書くフレームの前で止めます。なので触る前のフレームです）:

| 走り | 操作中のフレーム | スクロールの処理への到着 | そのあと速さが 0 になる | `SpareV` でない | 速さがそこのものでも 0 でもない | サブ速さがそこのものでない |
|---|---:|---:|---:|---:|---:|---:|
| TAS の 852 から | 239 | 239 | 3 | 0 | 0 | 0 |
| 操作からランダム（200 回） | 36,218 | 36,218 | 3,687 | 0 | 0 | 0 |
| 画面の左端へ（120 回） | 35,938 | 35,938 | 4,145 | 0 | 0 | 0 |
| TAS の 1002〜1091 フレーム目からランダム（400 回） | 45,809 | 45,809 | 1,633 | 0 | 0 | 0 |
| セレクトあり（100 回） | 10,475 | 10,475 | 523 | 0 | 0 | 0 |
| スタートあり（100 回） | 20,276 | 12,206 | 625 | 0 | 0 | 0 |

速さが 0 になる到着が多いので、`finV` の「または 0」は要ります。

## スクロールの処理からあと: 縦の 4 つのバイト

`vAfter` が求めていた 10 のバイトのうち 4 つは、`AfterKeep` の 2 つ目の歩きで変わらないと分かります（`Theorems/VertKeep.lean`）: 下向きの縦の力、ジャンプの始まりの高さ、ジャンプを止める値、A と B です。歩きはそれぞれを 1 つずつ、スクロールの処理からフレームの終わりまで追います。そのバイトへのどんな書き込みでも失敗し、フレームの終わりでまだ追えていることを求めます。歩きのガードはそのバイトを守ります。

```
kI               = VerticalForceDown, JumpOrigin_Y_Position, DiffToHaltJump, A_B_Buttons
vertE            = VerticalForceDown, JumpOrigin_Y_Position, DiffToHaltJump          （FrameKeep.vertE: guardE が守る。A_B_Buttons は spareE の中）
Prot_E           = stateE ∪ faceE ∪ spareE ∪ collE ∪ speedE ∪ vertE ∪ Prot_F          （faceE、stateE: 次の節から）
keep_end         : ctrlCheck ∧ kCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
                     →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ kI, y(frame(M, x)) = y(trM(k))
OnFrames.kAt     : 1 ≤ j < g ∧ k ≥ arr j ∧ pc(trM(k)) = PlayerSubs  →  ∀ y ∈ kI, y(seq j) = y(trM(k))          M = fm j, x = pad j
vAfter           : 1 ≤ j < J, j < g, k ≥ arr j, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ vHard, y(seq j) = y(trM(k))
vHard            = Player_Y_Position, Player_Y_MoveForce, Player_Y_Speed, Player_YMF_Dummy, Player_State          （VerticalForce: 2 つあとの節）
```

`vert_of` は `vKeep` の 9 つのバイトと A を `vAfter` と `kAt` から取ります。`kCheck` は `AfterKeep.hCheck` を `kI` のバイトでしたもので、ネイティブで 1.9 秒です。`numbersCheck` の一部です（`Numbers.vk`、`AreaRun.kv`）。

**スクロールの処理からあとで歩きが出会う書き込み**（`vert-after-bytes prot`: 10 のバイトそれぞれに 1 つの探索。そのバイトを追い、`keep.cleanE` のバイトに加えて守り、スクロールの処理での 8 つの状態から、ルーチン、モード、タスクへのアドレスでの書き込みで道を切ります）:

| バイト | 失敗 | 歩きが出会うアドレスでの書き込み |
|---|---:|---|
| `VerticalForceDown`、`JumpOrigin_Y_Position`、`DiffToHaltJump`、`A_B_Buttons`、`Player_YMF_Dummy` | 0 | なし |
| `VerticalForce` | 1 | ジャンプ台（`ChkForLandJumpSpring`） |
| `Player_State` | 6 | 当たり判定のルーチン（`SetPSte`: 2、`InitSteP`: 0）、つた（`PutPlayerOnVine`）、リフト（`SetCollisionFlag`） |
| `Player_Y_Position` | 11 | 着地（`LandPlyr`: 下位 4 ビットを 0）、上下に動くリフト（`PositionPlayerOnVPlat`）、ジャンプ台（`JumpspringHandler`、`DownJSpr`） |
| `Player_Y_MoveForce` | 9 | 着地（`LandPlyr`）、上下に動くリフト |
| `Player_Y_Speed` | 38 | 着地、頭をぶつける（`NYSpd`）、ブロック（`BumpBlock`、`BrickShatter`）、踏みつけ（`EnemyStompedPts`、`SBnce`）、リフト（`PositionPlayerOnVPlat`、`ProcLPlatCollisions`）、ジャンプ台（`BounceJS`）、死（`KillPlayer`） |

探索はそれぞれ約 62,000 歩、表は約 3,980 の状態、0.2 秒です。バイトを守らないと（`vert-after-bytes guard`）、A と B のほかはどのバイトも、行き先の分からない添字かポインタでの書き込み約 95 か所で失われます。

**残りの 6 つのうち 5 つが仮定のままである理由.**

* `Player_YMF_Dummy`、高さ、高さの端数、縦の速さは、スクロールの処理の前に、プレイヤー自身の縦の移動（`ImposeGravity`）が添字（添字 0）で書きます。なので、フレームのすべての命令の条件である `guardE` では守れません。スクロールの処理からあとの命令だけの条件は、新しいフィールドになります。
* `VerticalForce` はもう仮定ではありません: [下](#スクロールの処理からあと-縦の力)。
* 高さ、高さの端数、縦の速さ、状態: 地面から始まるどのフレームでも当たり判定のルーチンがこれらを書き、同じ値でまた着地させます。パート c の `RoomFall` は、着地で高さを分けてこの着地を証明しますが、その歩きは部屋の地図と敵がいないことを知っています。地上の歩きはどちらも知りません: 足の確認で地面が見つからないこと（状態は 2 のまま）、頭の確認でぶつかること（速さは 1 か 0）、敵を踏むこと、リフトやジャンプ台が動かすことがありえます。どれも地図か物体についての条件が要ります。

**本物のフレームで測ったもの**（`vert-after-real FM2 400`: 852 からのムービーと、操作からの自前の走り（ランダム、軽い押し、Select つき）の 1〜8 フレーム目。走りは、ルーチン、モード、タスクを書くフレームの前で止めます）:

| 走り | フレーム | `vAfter` が偽 | `Q` で地面の上 | `Q` で上昇中 | `Q` のあとにバイトが変わる |
|---|---:|---:|---:|---:|---:|
| 852 からのムービー | 8 | 0 | 1 | 7 | 1 |
| 操作からのランダム（400 本） | 3,200 | 0 | 2,411 | 789 | 2,411 |
| 操作からの軽い押し（400 本） | 3,200 | 0 | 2,321 | 879 | 2,321 |
| Select つき（200 本） | 1,600 | 0 | 1,180 | 420 | 1,180 |

`Q` で地面の上のとき、状態は 0、縦の速さと高さの端数は 0、高さの下位 4 ビットは 0 です。そのどのフレームでも、`Q` のあとに変わるのは状態だけです: `SetPSte` で 2、それから `InitSteP` で 0。着地は高さ、速さ、端数を、もとの値で書きます。`Q` で上昇中（状態 1、速さは負）なら、どのバイトも変わりません。`Q` でほかの場合は出てきません。

## スクロールの処理からあと: 向き、サブ速さ、当たり判定のビット

`Theorems/FaceKeep.lean`。スクロールの処理からフレームの終わりまでについて、2 つのことを証明します。どちらの歩きも、`AfterKeep` の歩きと同じく切り口から始まり、1 つ目の歩きでスクロールの処理まで行きます。

**向きとサブ速さ.** スクロールの処理からあとで、向きを番地で書く場所は 2 つです。ポールの当たり判定（`FlagpoleCollision`）は向きを書きますが、その道はそのあとルーチンを書くので、`noStore` が切ります。よじ登りのルーチン（`PutPlayerOnVine`）は、画面の左端の近くにいるとき彼を左に向けます。サブ速さを書くのはよじ登りのルーチンだけです。そのルーチンは、はじめに速さとサブ速さを 0 にします。歩きはそのバイトを `TaintRun` のカウンタ（`Env.rkI`）として追い、番地での書き込みの前で追うのをやめ（`CollideKeep.rkOff`）、フレームの終わりで、まだ追っているか、速さとサブ速さが 0 と分かっていることを求めます。

```
zI               = PlayerFacingDir, Player_X_MoveForce
faceE            = PlayerFacingDir, Player_X_MoveForce          （FrameKeep.faceE: guardE が守る）
finZ(B)          : B がまだそのバイトを追っている ∨ （B で速さとサブ速さが 0 と分かっている）
keepZ_end        : ctrlCheck ∧ zCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
                   →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ zI,  y(frame(M, x)) = y(trM(k)) ∨ (v(frame(M, x)) = 0 ∧ f(frame(M, x)) = 0)
CollideS.toR     : CollideS(M, Q, b, c) ∧ (f(b) = f(Q) ∨ (v(b) = 0 ∧ f(b) = 0)) ∧ (0 < v(Q) ∧ v(b) = v(Q) → P(b) = P(Q)) ∧ (¬c → P(b) = P(Q))  →  CollideR(M, Q, b)
```

* **向き.** `After.fd` はいまは `fd(b) = fd(Q) ∨ (v(b) = 0 ∧ f(b) = 0)` で、上の定理です（`MovesAt.face`）。向きがスクロールの処理のものなら、フレームは前と同じく `Pre` です。フレームが速さ 0 で終わるなら、`After.coll` からそのフレームは `Hit` です（`hit_of_stop`）: `coll` の 1 つ目の場合は `v(Q) = 0` を出すので `P(b) = P(Q) = P(a)`、2 つ目の場合は起こらず、3 つ目は当たりです。`OneFrame` は `Pre` のない `Hit` を許し、`step_of_one` はそれに当たりを出します。なので `T` までの clean な状態からのフレームでは、向きはもう仮定ではありません。
* **`J` より前のフレーム.** `J` より前に当たりは来てはいけません: `quiet_upto` は、これらのフレームがどれも `hstep` のとおりだと示します。なので `Pre` が要り、向きが要ります。歩きは、速さ 0 とサブ速さ 0 で終わるフレームのほかでは向きを出します。そこではフィールド `faceJ` が向きを求めます。そういうフレームでは彼は止まっています。
* **サブ速さ.** `collide` は `CollideS` です: 位置は前と同じに求め、サブ速さについては「速さ 0 とサブ速さ 0 で終わるフレームは、スクロールの処理でサブ速さが 0」だけを求めます。定理と合わせるとこれは `CollideR` で（`CollideS.toR`）、速さと合わせると `CollideE` です（`OnFrames.collideAt`）。`TopSpeed.Frame.impedeF` はどのフレームでも `f' = f₂` を求めるので、向きのように当たりでサブ速さを捨てることはできません。
* **歩きがこれ以上を出せない理由.** よじ登りのルーチンには、横の点がよじ登れるタイルの上にあるときに来ます。歩きは地図も物も知りません。プレイヤーの状態を守り、終わりで「まだ追っている、または状態が 0、1、2 でないと分かっている」（フィールド `state` がそれを除きます）を求めると、歩きは 1 つの道で失敗します: よじ登りのルーチンが状態をよじ登りにし、同じフレームのあとで台の当たり判定が状態を戻します（`collide-keep-check`）。

**スクロールの処理で右へ動くフレームの当たり判定のビット.** 当たり判定のルーチンはビットを `FF` にします。`ImpedePlayerMove` は片側のビットを消します。右をふさぐ側では、左へ動いていなければ速さも 0 にします。左をふさぐ側では、右へ動いていなければ速さも 0 にします。なので、スクロールの処理で左へ動いていないフレームは、`FF` か左をふさぐビットで終わるか、速さ 0 で終わります。

```
nl               = noLeft                                       （左をふさぐビット）
noLeftOK         : ∀ x,  x & nl = nl  →  x = FF ∨ x = nl           （256 のバイトの確認）
finB(B)          : B でビットがマスク nl の下で分かっている（左のビットのほかは 1） ∨ B で速さが 0 と分かっている
bits_end         : ctrlCheck ∧ bCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ bits(M) & nl = nl ∧ Arrive(M, x, n₀) ∧ once
                   →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs ∧ v(trM(k)) & 80 = 0  →  bits(frame(M, x)) ∈ {FF, nl} ∨ v(frame(M, x)) = 0
```

`once` は `subs_once` の結論です。これで、当たり判定のビットを求めていた `AfterR` は `AfterP` になります（`After.of`）。

* **部品.** 1 つ目の歩きは、当たり判定のビットを守り、マスク `nl` の下で見ながら、切り口からスクロールの処理まで行きます（`b1Cfg`: `AfterKeep` の 1 つ目の歩きを `CollKeep` のガードで）。なので、当たり判定のルーチンを早く出るフレーム（画面の行の外にいる）も、終わりでビットが `nl` の下にあります。スクロールの処理で、状態の中の速さの符号ビットを 0 にします（`toSign`）。2 つ目の歩き（`CollideKeep.walkKV`）は、`CollKeep` と同じく `ImpedePlayerMove` の `DEX` で `X` を分け、そこで速さを持つ `Y` を 2 つの `CPY #` で分けます（`splitYAt`）: `Y` の分かっているビットが許す値ごとに 1 つです。抽象機械の比較は、両方のバイトが分かっているときだけ結果の符号を知るので、分けないと歩きは両方の枝に進みます。それぞれの部分は自分の `Y` の機械を覆い（`cov_splitYAt`）、部分のあとの部分も覆います（`cov_comp`）。
* **表の鍵.** 鍵には速さの分かっているビットが入ります。速さが 0 と分かっている状態と、符号だけ分かっている状態を、1 つにしないためです。`ImpedePlayerMove` の中では `X` と `Y` も入ります。当たり判定のビットも鍵に入れると表は 4 倍になり（36,521 状態、964,629 歩、8 秒）、証明できることは増えません。
* **数.** 向き: 119,906 歩、表は 7,659 状態、失敗 0。追うのをやめるのはポールの書き込みとよじ登りのルーチンの書き込みです。サブ速さ: 119,889 歩、7,659 状態、失敗 0。`zCheck`: ネイティブで 1.6 秒。当たり判定のビット: 1 つ目の歩きは 1,769 歩、スクロールの処理での状態は 8 つで、どれもビットが `nl` の下で分かっています。2 つ目の歩きは 314,246 歩、表は 9,349 状態、失敗 0。`bCheck`: 2.5 秒。どちらも `numbersCheck` の一部です（`Numbers.zk`、`Numbers.bk`、`AreaRun.zk`、`AreaRun.bk`）。なので `pole_numbers` は約 4 秒長くなります。

**本物のフレームで測ったもの.** `collide-real FM2 200`（走りはルーチン、モード、タスクを書くフレームの前で止めます）。「到着」は、フレームがスクロールの処理に来ることです。

| 走り | 到着 | 速さ 0 とサブ速さ 0 で終わるフレーム | そのあと向きが変わる | 始まりが `FF` か左をふさぐビットで、そこで符号ビットが 0 | clean な状態から | `CollideS.f` が偽 | `CollideS` が偽 | `keepZ_end` が偽 | `bits_end` が偽 | `AfterP` が偽 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 852 からのムービー | 239 | 0 | 0 | 236 | 234 | 0 | 0 | 0 | 0 | 0 |
| 操作からのランダム（200 本） | 36,218 | 3,064 | 0 | 26,911 | 32,170 | 0 | 0 | 0 | 0 | 0 |
| 画面の左端へ（120 本） | 35,938 | 3,794 | 0 | 23,939 | 31,512 | 0 | 0 | 0 | 0 | 0 |
| ムービーの 1002〜1091 フレームからのランダム（400 本） | 45,809 | 5,532 | 0 | 36,135 | 42,908 | 0 | 0 | 0 | 0 | 0 |
| Select つき（100 本） | 10,475 | 767 | 0 | 8,041 | 9,904 | 0 | 0 | 0 | 0 | 0 |
| Start つき（100 本） | 12,206 | 1,215 | 0 | 9,389 | 11,445 | 0 | 0 | 0 | 0 | 0 |

`CollideS.f` を求めるのは到着の 10.2 % です: 速さ 0 とサブ速さ 0 で終わるフレームです。前の `CollideR.f` はすべてで求めていました。これらのフレームのどれでも、スクロールの処理のあとで向きは変わりません。

`pos-after-real FM2 200`: はじめの 5 種類の走り（128,679 フレーム）で、スクロールの処理のあとに位置の 3 バイトを変える命令を数えます。変えるのは 2 つの場所だけです: スクロールの処理の端の止め（`KeepOnscr`: ピクセルを 465 フレームで、ページを 450 フレームで）と、当たり判定のルーチンの押し（`ImpedePlayerMove`: ピクセルを 2,592 フレームで）。端数はどのフレームでも変わりません。フレームの終わりの位置は、スクロールの処理のものか、1 ピクセル少ない（左への押し）か、1 ピクセル多い（右への押し、または端の止め）か、2 ピクセル多い（端の止め。4 フレームで、どれも左へ動いている）です。

## スクロールの処理からあと: 縦の力

`vAfter` は前は縦の力も求めていました。スクロールの処理からあとで、縦の力を番地で書く場所は 1 つです: ジャンプ台への着地（`ChkForLandJumpSpring`）。着地はそのあとプレイヤーの状態を 0 にします。そのあと歩きが出会う状態への番地での書き込みは、台の当たり判定（0）とよじ登りのルーチン（3）だけです。なのでフレームは縦の力を保つか、書かれた値と状態 0 か 3 で終わります。フィールド `state` が 3 を除きます。

```
stateE           = Player_State, VerticalForce                    （FrameKeep.stateE: guardE が守る）
Prot_E           = stateE ∪ faceE ∪ spareE ∪ collE ∪ speedE ∪ vertE ∪ Prot_F
cv               = vfC                                            書き込みが書く値。探索から読む。確認と定理のパラメータ
finVF(B)         : B がまだ縦の力を追っている ∨ （B でそれが cv と分かっている ∧ B で状態が 0 か 3 と分かっている）
vf_end           : ctrlCheck ∧ vfCheck(v, c) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
                   →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  vf(frame(M, x)) = vf(trM(k)) ∨ (vf(frame(M, x)) = c ∧ st(frame(M, x)) ∈ {0, 3})
OnFrames.vfAt    : 1 ≤ j < g ∧ k ≥ arr j ∧ pc(trM(k)) = PlayerSubs  →  vf(seq j) = vf(trM(k)) ∨ (vf(seq j) = cv ∧ st(seq j) = 0)          M = fm j, x = pad j
VStep(a, b)      : vs(b) = vNext(a, b) ∨ (st(vNext(a, b)) = 0 ∧ vs(b) = vNext(a, b) で vf := cv)
vVar(w)          = [w, w で vf := cv]  （st(w) = 0 のとき）,    [w]  （ほか）
vNextAll(l)      = s ∈ l、A を押すか押さないか、abs ≤ v_top についての vVar(vstepV(s, A, abs)) の状態
vCheck_spec      : vCheck(n, l) ∧ u 0 ∈ l ∧ (∀ i < k, u (i + 1) ∈ vVar(vstepV(u i, A i, abs i)))  →  u k は箱の中          (1 ≤ k ≤ n)
```

* **歩き.** 速さの歩き（`CollideKeep.walkKV`）で、縦の力を追い、プレイヤーの状態を守ります。表の鍵には、縦の力を追うのをやめたあとの状態の分かっているビットが入ります。状態 0 と 3 を 1 つにしないためです。`vfC` は、探索で追うのをやめた最初の状態の縦の力です。Lean のファイルに値は書いていません。
* **ジャンプ台のバイトでなく状態を使う理由.** 第 14 回は、フレームの終わりで「まだ追っている、またはジャンプ台のバイトが 0 でないと分かっている」を求めました（`state` はそのバイトが 0 であることを求めます）。その歩きは 2 つの道で失敗します（200,638 歩、表は 13,449 の状態）。2 つは同じことです。着地はジャンプ台のバイトとジャンプ台のタイマーも、0 でない値にします。ジャンプ台自身のコードは、ジャンプ台が入っている敵の枠ごとに動きます。歩きは枠の中身を知りません。そのコードはタイマーが 0 ならバイトに 1 を足し、それが何回か続くとバイトを 0 に戻します。本物の機械では着地のあとタイマーは 0 でないので、足されません。歩きはタイマーを忘れます: 表は守るバイトだけを覚えます。タイマーも守るとその歩きは閉じます（120,856 歩、表は 7,781 の状態、失敗 0。タイマーの RAM の番地を付けた `face-keep-check ADDR`）。しかしタイマーは `guardE` に入れられません: NMI のタイマーのループは、タイマーが 0 でなければ添字でそれを減らします。なので各命令のその条件は「どのフレームでもタイマーは 0」を意味します。プレイヤーの状態にはそういうことはありません。
* **モデル.** 地面の上では、縦の一歩は縦の力を読まず、ジャンプの始まりが縦の力を書き直します。なので `J` より前のフレームが地面の上で終わるとき、縦の力はモデルのものでなくてもかまいません。`VStep` はそこで書かれた値を許し、`vNextAll` は両方の状態を追い（`vVar`）、`vCheck` は両方で箱を確かめます。`box` が読むのは `vNext` の高さ、縦の速さ、状態だけで、どちらの場合も同じです。
* **数.** 歩き: 178,839 歩、表は 11,507 の状態、失敗 0。`vfCheck`: ネイティブで 1.7 秒。`numbersCheck` の一部で（`Numbers.vfk`、`AreaRun.vfk`）、`vCheck` は `vfC` を受け取ります。なので `pole_numbers` はこの 2 つで約 4 秒長くなります。
* **測ったもの.** 本物の走りの 1〜8 フレーム目では、スクロールの処理のあとで縦の力は変わりません（`vert-after-real FM2 400`: 8,008 フレーム、[上](#スクロールの処理からあと-縦の-4-つのバイト)）。`guardE` の新しい 4 つのバイト（`faceE`、`stateE`）はいっしょに測りました: `keep-frames-check FM2 100`（地上の 224,813 フレーム。触るフレームとポーズのあるフレームも含む）: どの走りでも、添字かポインタでの守るバイトへの書き込みはありません（終了コード 0）。`open-real-check FM2 300`（パート a のフレーム）: 条件に合わないフレームは 0。`up-clean-u FM2 quick`: 終了コード 0（`guardE` が守るのは 67 バイト、合わせたガードはこの回のパート b の 1 バイトを入れて 143 バイト）。`open-air-search all`: 失敗 0、表は前と同じ 95,459 状態、`airCheck` は真。`phase-frame-check`: 確認は真で、2 つ目の歩きの表は 45,022 状態です（前は 45,260）。

## スクロールの処理での覚えている速さ

`ImposeFriction` は最後に `|v|` を覚えている速さ（`Player_XSpeedAbsolute`）に書きます。地上ではどのフレームでも動きます。空中では左か右を押すときだけ動きます。押さないときは、スクロールの処理まで速さも覚えている速さも変わりません。なので、プレイヤーのルーチンで覚えている速さが `|v|` なら、スクロールの処理でもそこでの `|v|` です。プレイヤーのルーチンでのことは `Clean(a)` から出ます。

```
storedOK    : 4608 の場合のそれぞれで、frictionCheck の機械と並べた ImposeFriction。出口で速さと覚えている速さ。
              と、移動のルーチンでの切れ目のそれぞれから、どちらのバイトも書かずにスクロールの処理まで行く 1 つの機械の歩き
stored_path : modelOK ∧ frictionCheck ∧ storedOK ∧ AtFrame(R) ∧ abs(R) = |v(R)|
              →  ∃ k,  pc(stepN(k, R)) = PlayerSubs ∧ abs(stepN(k, R)) = |v(stepN(k, R))| ∧ InFrameN(R, k)
subs_once   : keepH の条件  →  ∀ k k' ≥ n₀,  pc(trM(k)) = PlayerSubs ∧ pc(trM(k')) = PlayerSubs  →  k = k'
storedQ_of  : modelOK ∧ frictionCheck ∧ storedOK ∧ AtCtrl0(R) ∧ Clean(a) ∧ v(R) = v(a) ∧ bits(R) = bits(a) ∧ time ∧ idleAt(idle) ∧ once
              →  ∀ k ≥ n₀,  pc(trM(k)) = PlayerSubs  →  abs(trM(k)) = |v(trM(k))|
```

`R = trM(n₀)` はプレイヤーのルーチンでの機械、`once` は `subs_once` の結論です。

* **歩き.** `ImposeFriction` までは `frame_path` の歩き（`caseOK`、`frameCaseOK`）です。`ImposeFriction` では本物の機械を `TopSpeed.frictionCheck` の機械と並べて動かします。その機械は、`m0` に本物の機械の速さ、サブ速さ、足す値、2 つの上限、当たり判定のビットを入れたものです。その確認は、ルーチンのあとの覚えている速さが `|v'|` だと言います。戻ってから移動のルーチンまでは `fricOK` の歩きで、覚えている速さも見るようにしました（`watchM`）。移動のルーチンからスクロールの処理までは新しい 1 つの機械の歩き（`storedTailOK`）で、速さと覚えている速さを見ます。移動のルーチンでの切れ目は 2 つ（`tailsOf`）で、どちらからもプレイヤーのルーチンのスタックでスクロールの処理に来ます。
* **どの到着か.** `stored_path` はある歩数でスクロールの処理に来ます。移動（`move_model`）は自分の歩数で来ます。`After` はプレイヤーのルーチンのあとのどの到着についても言います。`AfterKeep` の歩きは、到着が 1 つしかないことを示します: 1 つ目の歩きは最初の到着で止まり、2 つ目の歩きはほかの到着で失敗します（`subs_once`。`keepH` も同じ定理 `keepH_once` から証明するようにしました）。なのでどれも同じ命令です。
* **条件.** `AtFrame(R)` は `|v(R)| ≤ v_top` と、当たり判定のビットが `TopSpeed.collBits` にあることを要ります。どちらも `Clean(a)` から出ます: `inD` と、ビットが `FF` か `noLeft` であることです。`frictionCheck` は [最高速の上限](../0-0/0-1-TopSpeed-ja.md) の確認です。ネイティブで約 55 秒かかり、非公開の証明にもうあります（`top_frictionCheck`）。なので計算し直さず、`SurfaceRun.Statement` のフィールド `fric` として渡します。
* **数.** `storedOK`: 4608 の場合、失敗 0、プログラムで 357 ミリ秒。`numbersCheck` の一部です（`Numbers.storedW`）。

## 機械から読むフレーム

`fr j` は前は `Run` のデータで、フィールド `reads` が、`seq (j − 1)` のバイトで始まり `seq j` のバイトで終わると言っていました。なので `reads` には書かれていない主張が入っていました: 本物の各フレームは `TopSpeed.Frame` である、です。いまは `fr` は定義で（`SurfaceFrames.frOf`、`Run.fr`）、その主張は 1 つのフレームか 1 つの機械の条件から証明です。

```
CollideE(B₀, Q, b) : (v(b) = v(Q) ∨ v(b) = 0) ∧ f(b) = f(Q)
                    ∧ (P(b) = P(Q) ∨ P(b) = P(Q) − 256 ∨ (P(Q) ≤ P(b) ≤ B₀ + 256 ∧ v(Q) ≤ 0))
ReadH(M, x, n₀)   : modelOK ∧ frictionCheck ∧ AtFrame(R) ∧ R の横の 8 バイトは M のもの ∧ InTime ∧ far(M)
ReadE(M, x, n₀, B₀) : ReadH(M, x, n₀) ∧ スクロールの処理に来るどの Q でも CollideE(B₀, Q, b)      （B₀ は数えるフレームの 1 つ前の終わりの基点 base(seq (j − 1))）
frameE(a, M, x, n₀) = frame_readE の Frame で、始まりは a のもの        ReadE で、M が a の横のバイトを持つとき
                      a の始まりで止まるフレーム                         そうでないとき
frameH(a, M, x, n₀) = read_move の Frame で、始まりは a のもの          ReadH で、M が a の横のバイトを持つとき
                      （スクロールの処理で終わる: v' = v₂, f' = f₂, P' = P₂）
                      a の始まりで止まるフレーム                         そうでないとき
frOf j = frameE(seq (j − 1), fm j, pad j, arr j)    j < g
         frameH(seq (j − 1), fm j, pad j, arr j)    j ≥ g
farN(m) = min(⌊(P(m) − 2048) / (16·v_top + 256)⌋, ⌊(2²⁴ − 2049 − P(m)) / (16·v_top)⌋)          B.m で 745
```

`AtFrame(R)` は `FrameModel.frame_read` が要る、プレイヤーのルーチンでの状態です。`AtCtrl0` から覚えている速さを除き、当たり判定のビットが `collBits` にあることと `|v| ≤ v_top` を加えたものです。`InTime` はフレームの時間です（[`FrameTime`](c-7-1-1-FrameTime-ja.md)）。`CleanK` の条件 `time` から出ます。

```
read_move         : ReadH(M, x, n₀)  →  v, f, P が M のものの Frame があり、スクロールの処理に来る k ≥ n₀ で v₂, f₂, P₂ は trM(k) のもの
frame_readE       : ReadE(M, x, n₀)  →  v, f, P が M のもの、v', f', P' がフレームの終わりのものの Frame があり、P₂ − 256 ≤ P'
frameE_move       : ReadE(M, x, n₀)  →  スクロールの処理に来る k ≥ n₀ があり、frameE の v₂, f₂, P₂ は trM(k) のもの      （14 回目、パート f の StopRead のため）
OnFrames.readH    : 1 ≤ j ≤ g ∧ |v(seq (j − 1))| ≤ v_top ∧ far(seq (j − 1))  →  ReadH(fm j, pad j, arr j) ∧ fm j は seq (j − 1) の横のバイトを持つ
OnFrames.readAll  : g ≤ farN(B.m)  →  ∀ d < g,  |v(seq d)| ≤ v_top  ∧  (d < farN(B.m)  →  P(B.m) − (16·v_top + 256)·d ≤ P(seq d) ≤ P(B.m) + 16·v_top·d)
OnFrames.reads    : g ≤ farN(B.m)  →  Reads(g, seq, frOf)                （前のフィールド reads）
OnFrames.touchMove: P₂(frOf g) と v₂(frOf g) は、スクロールの処理に来るある k ≥ arr g での P と v
```

* `frame_readE` は `FrameModel.frame_readR` の `Collide` を `CollideE` に変えたものです。`Collide` は 3 つ目の場合で `P(b) = P(Q) + 256` を求めます。画面の左端では、スクロールの処理が彼を端に置くので、`P(b) − P(Q)` が 512 になることがあります（[画面の左端](#画面の左端)）。`CollideE` は `TopSpeed.Frame.impedeP` と同じくこれを許し、`P(Q) ≤ P(b)` を求めます: 端は彼を右へ押し、左へは押しません。
* `readH`: `CtrlKeep` の歩き（`ctrl_keep`）がルーチンまで `keepA` の 25 バイトを保ち、`lag` のフレームも保ちます（`OnFrames.lagKeep`。触るまでのどのフレームでもになりました）。エリアの値と当たり判定のビットは `AreaRun` から出ます（`OnFrames.areaRun`: `areaAll` と `collAll`）。`AtFrame` の残りは `state` から出ます。
* `readAll`: フレームについての帰納法です。操作できるとき `v = 0` です。触る前の各フレームは `ReadE` を満たす `frameE` です。なので `Frame.bound` が `|v'| ≤ v_top` を保ちます。1 フレームで右へは `16·v_top` 以下、左へは `16·v_top + 256` 以下しか動きません（`P' ≥ P₂ − 256 = P + 16·v₂ − 256`）。なので最初の `farN` フレームでは、位置は範囲の両端から遠いままです。`readAll`、`readE_at`、`reads`、`touchMove` は `g ≤ farN(B.m)` を求めるので、触る前のどのフレームもその中です。それより後に触る走りは [下](#遅く触る走り) です。
* `reads`: 始まりは定義で `seq (j − 1)` のものです。触る前のフレームの終わりは、`frame_readE` で `frame(fm j, pad j)` のもので、それは `seq j` です（`keep.ends`）。
* 触るフレーム `g` は `Frame` の終わり方をしません。触ることが彼を動かします。`frOf g` はスクロールの処理までのフレームです。`touchMove` は、`P₂(g)` がスクロールの処理に来たときの位置だと言います。`Run` のフィールド `moved`（パート f）は、ルーチンを書く前のどの到着でもこの位置だと言います。

**測ったもの.** `surface-read-check FM2 200`（プログラム、終了コード 0、CPU で約 2 分 15 秒）。数える各フレームで、前の数えるフレームの終わりから、`state`、`coll`、`|v| ≤ v_top`、`far`、`lag` のフレームが 25 バイトを保つこと、ルーチンでの `AtFrame`、ルーチンまでの横のバイト、フレームの時間、スクロールの処理への到着を見ます。触る前のフレームでは、スクロールの処理へのどの到着でも `CollideE` も見ます。走りの最後のフレームは操作できない状態で終わります（触る、死ぬ）。これは触るフレームとして、`CollideE` 以外を見ます。

| 走り | 数えるフレーム | `lag` | 最後のフレーム | 失敗 | `CollideE` だが `Collide` でない | 1 フレームで動く最大（右、左） |
|---|---:|---:|---:|---:|---:|---|
| TAS の 852 から | 240 | 0 | 1 | 0 | 0 | 640, −224 |
| 操作からランダム（200 回） | 53,724 | 0 | 94 | 0 | 2 | 640, −592 |
| TAS のフレームからランダム | 32,715 | 0 | 65 | 0 | 0 | 640, −640 |
| セレクトあり、スタートあり | 28,689 | 8,070 | 91 | 0 | 3 | 640, −592 |
| 左端へ走る | 53,398 | 0 | 130 | 0 | 13 | 640, −640 |
| 遅く触る、長いジャンプ | 34 | 0 | 1 | 0 | 0 | 640, −16 |

操作できるときの位置は 669696 です（`B.m` と TAS）。`v_top = 40` です。なので `farN(B.m) = ⌊667648 / 896⌋ = 745` です。TAS は 240 フレーム目にポールに触ります。746 フレーム目以降に触る走りは、遅く触る走りです（[下](#遅く触る走り)）。

## 当たり判定のビット

`bits(m)` は当たり判定のビットです。前のフィールド `coll` は、触る前の各フレームの終わりで `bits ∈ collBits = {FC, FD, FE, FF}` だと言っていました。いまはこれは定理です。

当たり判定のルーチンはビットを `FF` にします。`ImpedePlayerMove` は終わりで `X` で決まるビットを消します。そこの `X` はどの道でも 1 か 2 です: ルーチンは横の確認の数え役（ゼロページのバイト）を読み、1 を引き、それが 0 なら `X = 1`、そうでなければ `X = 2` にします。画面の行にいないときは、ルーチンはビットを保ちます。

歩きが表の状態からそこに来るとき、歩きは数え役を知りません: 表はそのバイトを忘れます。すると `dex` のあと `X` は分かりません。ゼロフラグでの分かれ道は両方に進み、ゼロフラグが立つほうの道で、歩きは `X = 0` を知りません。なので消すビットが分からず、歩きは 4 つのフレームの終わりで失敗していました（第 11 回）。

いまは歩きがその `dex` で `X` を 256 の値に分けます（`splitXAt`）。値のそれぞれが 1 つのかけらで、機械の `X` のかけらがその機械を覆います（`cov_splitXAt`）。表のキーは、分けたところからルーチンの終わりまで `X` を持ちます。なのでかけらはまたつながりません。

```
CollOK(m)        : bits(m) & FC = FC
collBitsOK       : ∀ x,  x & FC = FC  →  x ∈ collBits                    （256 のバイトの確認）
SpareC(m)        : m の添字かポインタでの書き込みは、当たり判定のビットを書かない        CleanK_E の一部（spareC_of）
coll_end         : ctrlCheck ∧ collCheck(v) ∧ StartK(m) ∧ (∀ n, CleanK_E(trm(n))) ∧ (∀ n, ¬CtlStore(trm(n)))
                   ∧ AreaOK(v, m) ∧ CollOK(m)  →  CollOK(frame(m, i))
OnFrames.collAll : CollOK(seq 0)  →  ∀ n < ix g,  CollOK(all n)
```

`CleanK_E` は `guardE` の `CleanK`、フィールド `keep.cleanE` です。この回から `guardE` は当たり判定のビットも守ります（`FrameKeep.collE`）。歩きの guard は、当たり判定のビットも守る `guardF` です。`guardE` が守るバイトはそれが守るバイトを含むので、`CleanK_E` だけからそれが出ます（`cleanC_of`）。前のフィールド `spareC` の `SpareC` は `CleanK_E` の一部です（`spareC_of`。`CleanK` が何も求めないプレイヤーの端数の書き込みのほか）。プレイヤーのルーチンに来るフレームは歩きです（`walkKX`: 各ステップの前に分けることを足した `FrameKeep.walkKC`）。そこに来ないフレームはビットを保ちます（`CtrlKeep.keep_of_noCut`）。操作できるとき `bits = FF` です（`B.m` での `numbersCheck` と `Start.bits`）。`collAll` は、数えるか数えないかによらず `keep` のフレームについての帰納法で、触るフレームの前のフレームの `noStore` と `cleanE` を使います。`readH` は、それと `collBitsOK` から `bits(seq (j − 1)) ∈ collBits` を得ます。

**測ったもの.** プレイヤーのルーチンからの探索。ビットはマスク `FC` で見ます。プログラムで:

| 探索 | ステップ | 表 | 失敗 | 時間 |
|---|---:|---:|---:|---:|
| 第 11 回（`coll-cut-check`） | 404,240 | 22,446 | 4 | 1.4 秒 |
| ゼロページのバイト 0 を守り、キーに入れる（`coll-key-check 0`） | 106,190,191 | 3,719,813 | 267 | 527 秒 |
| `X` を分ける、`X` はキーにない | 411,125 | 22,457 | 4 | 3.4 秒 |
| `X` を分ける、`X` をキーに入れる（`coll-split-check`） | 615,303 | 38,413 | 0 | 3.9 秒 |

バイト 0 はゲーム全体の一時バイトです。なのでキーに入れると表は多くの状態に分かれ、それを守ることも 267 か所で失敗します。なので `X` を分けるほうを使います。`collCheck` はプログラムで約 5 秒です。これは `numbersCheck` に入るので（`collCheckAll`）、`pole_numbers` は約 5 秒長くなります。

`coll-real FM2 200`（ムービーの 852 から、と操作からの自分の入力。走りは、ルーチン、モード、タスクに書くフレームで止めます）:

| 走り | フレーム | `SpareC` でない | `CollOK` で始まり `CollOK` でなく終わる | `CollOK` でなく終わる | 終わりの値 |
|---|---:|---:|---:|---:|---|
| TAS の 852 から | 239 | 0 | 0 | 0 | FD, FE, FF |
| 操作からランダム | 36,218 | 0 | 0 | 0 | FD, FE, FF |
| セレクトあり | 10,475 | 0 | 0 | 0 | FE, FF |
| スタートあり | 20,276 | 0 | 0 | 0 | FD, FE, FF |

`cleanE` は触るフレームでも求めるので、当たり判定のビットを守る `guardE` は触るフレームでも確かめました。`keep-frames-check FM2 100`（[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md) の確認。新しい `guardE` で）: TAS、操作からランダム 100 回、TAS の 1002〜1091 フレーム目からランダム 400 回、画面の左端へ 120 回、ポーズあり 500 回。約 225,000 フレーム、触るフレーム 457。`Plain` でない書き込み 0、失敗 0（終了コード 0、約 4 分）。

`guardE` を使う歩きは [`PhaseFrame`](0-5-2-1-1-PhaseFrame-ja.md) の歩きです（`guardPh` は `guardE` に 2 バイト足したもの）。守るバイトが 1 つ増えたので、その 2 つ目の歩きの表は 38,386 から 45,392 状態に増え、`phaseCheck` はプログラムで 2.8 秒から 3.1 秒になりました。非公開の `Proof.PhaseFrame` は通ります（終了コード 0）。ほかの歩きは `guardF` か `guardK` を使うので変わりません。

## 遅く触る走り

フレームを機械から読めるのは、最初の `farN(B.m) = 745` フレームです（`readAll`）。なのでそれを読む定理は `g ≤ farN(B.m)` を求めます: `readAll`、`readE_at`、`reads`、`touchMove`、`surface_of_frames`、[`PoleJoin`](f-5-PoleJoin-ja.md) の `Run.reads`、`Run.next`、`hB_run`、`base_late`、`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle`（新しい引数 `hg`）。前のフィールド `farLate` が、それより後のフレームの位置の範囲を与えていました。

それより後に触る走りにはフレームは要りません: フレームの数が上限を与えます。タイマーは 2 フレームに 1 度までしか進まないので、遊ぶフレームが 2 つ増えると、`CastleToLevel.sum_ge` の和 `E + T` は 1 以上増えます。

```
ticks_add_twice  : 2 ≤ q  →  ticks(q, p + 2k) ≤ ticks(q, p) + k
sum_ge_late      : sum_ge の P1, X1, P2, X2, E, T の条件と 492 ≤ P3  →  1588 + j ≤ E + T          （W は何でもよい）
level_ge_late    : 同じもの、と level_ge の D, c, L の条件  →  1748 + j ≤ L
level_ge_of_late : Route.Run ∧ 368 ≤ pipe.E ∧ room.C + 111 ≤ room.E ∧ 492 ≤ pole.g ∧ pole.g < pole.c  →  1748 + j ≤ L
pole_far_count   : 492 ≤ farN(B.m)                                        （非公開の証明で native_decide。farN(B.m) = 745）
```

492 の理由: `sum_ge` は 3 つ目の区間から `W + P3 − ticks(P3) + ticks(240) ≥ 366` を要ります。`ticks_add_twice(240, 126)` は `ticks(492) ≤ ticks(240) + 126` を与えます。なので `P3 = 492` からは、`W = 0` でも `P3 − ticks(P3) + ticks(240) ≥ 366` です。

`route_1_1` は 2 つの場合に分けます。`g ≤ farN(B.m)` なら前と同じです（`hg` を渡す `pole_touch_castle`）。そうでなければ `pole_far_count` で `492 ≤ g` で、`g < c` は `PoleJoin.Run.afterTouch` です。なので `farLate` はなくなり、代わりに仮定するものはありません。

## 走り全体の文は定理

```
step_of_one       : Clean(a) ∧ OneFrame(a, b)  →  (Follow(a, b) ∧ Clean(b)) ∨ Hit(a, b)
OnFrames.reads    : OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaRun(v) ∧ v(seq 0) = 0 ∧ P(seq 0) = P(B.m)  →  Reads(g, seq, frOf)
next_of_reads     : Reads(g, seq, fr)  →  ∀ j ∈ [1, g), Next(fr j, fr (j + 1))
quiet_upto        : 1 ≤ j < J, j < g  →  フレーム 1..j は Follow ∧ seq 0..j は Clean ∧ bits(seq j) = FF
                                         ∧ フレーム 1..j は VStep ∧ seq 0..j は HaltOK
surface_of_frames : OnFrames ∧ Start(B, seq 0) ∧ (∀ n < ix g, StartK(all n)) ∧ noHitCheck ∧ numbersCheck ∧ J ≤ T
                    →  ∃ w h, Surface(w, h)
Run.next, Run.startP, Run.startV                                 PoleJoin
```

| 前の仮定 | 今 | どこから |
|---|---|---|
| `model`: `j < h` で `P'(j) ≤ P_A + d(w)` | 定理 | `one_of_frames`。`w` は `inp j` の列、`h` は `Follow ∧ Clean` でない最初のフレーム |
| `hit`、`stop` | 定理 | `OneFrame` の `Hit` |
| `box`、`off`: `J` の前にぶつからない | 定理（`Surface.first : J ≤ h`） | `box`、`vert_of`、`moves`、距離の上限（`dist_abs`）、高さの探索（`vCheck`） |
| `next` | 定理 | `OnFrames.reads`。両方の端を同じ機械から読む |
| `startP`、`startV` | 定理 | `Start`。下の節 |
| `mem`、`long` | 定理 | `inAt_mem`、`w` の作り方 |

**箱の中.** 1〜8 フレーム目の `x` は仮定ではありません。`|d(w)|` の上限から 4 ピクセル以内です（`dl`、左へは速さのバイトが 1 大きくなるので `dbound` より少し大きい）。高さも仮定ではありません。`vCheck` は `vs(B.m)` から A の有無と 0 から最高速までの覚えている速さの全部で 8 フレーム `vstepV` を動かし、全部が箱の中であることを確かめます。

## 操作できるときの状態

`Start(B, m)` は 1 つの機械についての文です。

```
Start(B, m) : hs(m) = hs(B.m) ∧ P(m) = P(B.m) ∧ abs(m) = abs(B.m) ∧ bits(m) = bits(B.m) ∧ vs(m) = vs(B.m)
              ∧ AreaType(m) = AreaType(B.m) ∧ SwimmingFlag(m) = SwimmingFlag(B.m) ∧ PlayerChangeSizeFlag(m) = PlayerChangeSizeFlag(B.m)
              ∧ A_B(m) = A_B(B.m) ∧ PrevA(m) = PrevA(B.m)
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
* `Moves` を確かめたどのフレームでも、新しいフィールドと、新しい歩きが証明することも確かめました: `AfterP`、`CollideS`、向きとサブ速さ（`keepZ_end`）、スクロールの処理で速さの符号ビットが 0 のときの当たり判定のビット（`bits_end`）。1〜8 フレーム目では `faceJ` と、5 つのバイトの `vAfter` も確かめました。違いはありません。どのフレームでも向きが等しいという前の `After` も、これらのフレームで成り立ちます。
* 前のフィールド `unpaused`、`lagPaused`、`spare`: ポーズで終わる操作中の数えるフレーム、ポーズでなく終わる `lag` のフレーム、`spareI` の 4 バイトへの添字かポインタでの書き込みのあるフレームは、どれもありません。プレイヤーのルーチンに来る `lag` のフレーム（`OnFrames.lagNo` が証明すること）と、エリアの種類、泳ぎのフラグ、大きさの変化を変える操作中のフレーム（`OnFrames.areaAll` が証明すること）もありません。Start ありの `lag` のフレーム 8,070 も含めて、どの走りでもすべて 0 です。証明の機械はエリアの種類 1、泳ぎのフラグ 0、大きさの変化 0 です。
* 全部のフレームで、プレイヤーのルーチンが読む入力は両端から読む `readIn(a, b)` と同じです（前のフィールド `input`）。違いは 0 です。
* 1〜8 フレーム目の 3,194 フレームのうち 2,375 で、スクロールの処理からフレームの終わりまでのあいだに縦のバイトが別の値になり、終わりには戻っています。地面の上では当たり判定のルーチンが `Player_State` を 2 にして、また着地させます。なので `vAfter` は、これらのバイトへの書き込みを許さない歩きからは出ません。4 つのバイトでは出ます: スクロールの処理からあとに書かれません（`OnFrames.kAt`、[上](#スクロールの処理からあと-縦の-4-つのバイト)）。縦の力をそこで書くのはジャンプ台への着地だけです（`OnFrames.vfAt`、[上](#スクロールの処理からあと-縦の力)）。
* 押している側がふさがれたフレームは 329 です（操作から 3、階段のまわり 326）。全部 `OneFrame` で、全部 `Moves` を満たします。移動の処理に来たとき、182 はモデルの速さで、147 はモデルの速さが 0 でないのに速さ 0 です（`move_masked` の 2 番目の場合。種類の列では `Hit` に数えます）。この 147 は `Pre ∧ Coll` でなく、`MaskStop` が要ります。前にこのページは要るものは 0 と書いていましたが、それは誤りでした。`bits(R) = bits(a)` が成り立たないフレームはありません。
* `lag` のフレーム 8,070 では、ここで読むバイトは変わりません。なので `seq j` のあとに `lag` のフレームがあっても読む値は同じです。はみ出すフレームはこれらの走りにありません。
* 切り替え: TAS の入る状態と `E` から、Start なしのランダムな入力で 201 回。全部 282 フレーム以上で操作でき、操作の前に `left` が 0 になることはなく、操作のときの状態は全部 `Start` を満たします。
* 測り方: 操作できない機械で終わるフレーム（死ぬ、旗に触る）はフィールドの外なので数えません。そこで `Follow` と `Hit` は成り立ちません。そういう走りは `Run` ではありません。
* `after-real FM2 100`（TAS の 852 からと、操作からの自分の走り 300 回: ランダム、Select あり、Start あり。操作中のフレーム 35,802。ルーチン、モード、タスクを書くフレームで走りを止める）: `SpareE` はどの命令でも成り立ちます。`PrevOK` はどのフレームの始まりと終わりでも成り立ちます。`hI` の 3 バイトはフレームの終わりでスクロールの処理でのものと同じで、プレイヤーのルーチンのあとスクロールの処理に 2 度来るフレームはありません。Clean な状態からの 31,949 フレームで `storedQ` と `After` は成り立ちます。Clean でない状態からの 338 フレームで `storedQ` は成り立ちません。そこでは `moves` を聞きません。

## 最初のフレームを抽象機械で

最後の段の操作できる状態から 1 フレームを歩いてみました（Lean には入れていません）。

| 知っていること | 歩数 | 失敗 |
|---|---:|---:|
| パッドが不明 | 27,292 | 5（`FindEventMusicHeader+2`） |
| `EventMusicQueue = 0`、パッドが不明 | 2,288 | 4（`JumpEngine+18`） |
| `EventMusicQueue = 0`、パッドは Start なしの 128 通りのそれぞれ | 739,183 | A なしの 64 通りで 1 回（`BlockBufferCollision+43`） |
| さらに `PlayerSize` を場合分け | 1 つの場合に約 840,000 | 0、4 つの場合で約 3 秒 |

なのでフレーム 1 だけなら閉じます。これは 233 フレームのうちの 1 つで、次のフレームの状態の数は増えるので、入れていません。

## プレイヤーの状態とジャンプ台（証明していない）

`state`（前の `Moves.state`）は前のフレームの終わりで 2 つの値を求めます: `Player_State` ∈ {0, 1, 2} と `JumpspringAnimCtrl` = 0 です。触る前の操作中のフレームで（`noStore` のもとで: ルーチン、モード、タスクを番地で書かない）、これらを書くのは次の書き込みです。

* ジャンプ台のバイト: 0 でなくするのは `ChkForLandJumpSpring` だけです。足の判定が、着地させる道（`LandPlyr`）でそれを呼び、そこのタイルが 2 つのジャンプ台のタイルのどれかなら書きます。ジャンプ台の物のコードは、バイトが 0 でないときだけ書きます。
* 状態 3（よじ登り）: `PutPlayerOnVine` だけです。当たり判定の横の判定が、タイルの真ん中の部分の横の点がポールのものでないよじ登りのタイルのとき、そこに来ます（`HandleClimbing`）。ポールのタイルはルーチンも書くので、そのフレームは触るフレームです。足の判定と頭の判定のよじ登りの確認は状態を書きません。ほかの 3 の書き込みは、エリアの始まり、つたからの入り、つたを登るルーチンにあり、プレイヤーの操作にはありません。そのようなフレームでのほかの状態の書き込みは 0、1、2 を書きます（ジャンプは 1。当たり判定は 0、1、2。台は 0）。パワーアップとやられの書き込みはルーチンも書くので、`noStore` が切ります。

なので、当たり判定が読むタイルについての次の 1 フレームの条件があれば、2 つの値が出ます: 足の判定の着地のタイルはジャンプ台のタイルでなく、タイルの真ん中の部分の横の点はポールのもの以外のよじ登りのタイルでない。それがあっても、証明には次の手順が要ります。

* ジャンプ台: プレイヤーのルーチンからの歩きは、バイトを 0 として見て守り、そこを番地で書く命令で各道を止めると閉じます: 84,594 歩、失敗 0、表は 7,217 状態、0.4 秒（プログラム `spring-cut-check`）。バイトへの書き込みで止まるのは `ChkForLandJumpSpring` の中の 1 つだけです（2 回。ほかの 8 つの止まりは `noStore` の書き込み）。前の探索はどの道も止めず（これらの書き込みでも `noStore` の書き込みでも）、終わりませんでした（このページで 9 分、6.8 GB。パート a で 4 分、21.7 GB）。
* 状態: 歩きは、1 つのバイトをマスクのもとの 1 つの値で見ます。{0, 1, 2} はそのような集まりでないので、歩きに新しい見方か、値で分けてフレームの終わりで集まりを確かめることが要ります。試していません。
* どちらのバイトも、添字かポインタでの書き込みの条件（`spareE` のような）に加えることが要ります。

これは `state` より小さいか? いいえ。`state` は数えるフレームごとに、1 つの機械の 2 バイトです。上の条件は、触る前のどのフレームにも（数えるものも数えないものも）、それぞれ 6 つまでのタイルの読み（足 2 つ、横の点 4 つ）についてで、添字かポインタでの書き込みの条件に 2 バイト足します。歩きがあれば `state` が出ますが、`state` からこれらは出ません。よい点は、これらが地図についての条件なので、地上のブロックのバッファのモデルがあれば証明できることです。`state` は、これらの歩きなしには地図から出ません。なので `state` はそのままにします。

本物のフレームで測ったもの（`spring-real FM2 100`: TAS の 852 からと、操作からの自分の走り: ランダム、Select あり、Start あり。操作中のフレーム 35,731。ルーチン、モード、タスクを書くフレームで走りを止める）: ジャンプ台のバイトを書く命令はなく、状態に 3 を書く命令もなく、添字かポインタで状態を書く命令もなく、状態 3 かジャンプ台のバイトが 0 でない状態で終わるフレームもありません。

## 前提（Lean では証明していない）

* `moves`: 移動の外の部分。プレイヤーのルーチンまでは、操作中のフレームの始まりと `CleanK` から証明です（`ctrl_keep`）。ルーチンに来ることと、数えないフレームが 25 バイトを保つことも証明です。移動のあいだにフレームが終わらないこと（`CleanK` から）と、位置が端から遠いこと（前のフレームから）も証明です。前のフレームの A の 7 ビット目（`OnFrames.prevAll`）と、スクロールの処理からあとの 3 バイト（`AfterKeep.keepH`）も証明です。スクロールの処理での覚えている速さも証明です（`MovesAt.stored`）。残るのは、スクロールの処理で右へ動くフレームの位置（`AfterP`）です。前のフレームの終わりの値は、いまはフィールド `state` です。移動そのものは、押している側がふさがれていても証明です（[`FrameModel`](../0-0/0-3-2-FrameModel-ja.md)）。
* `unpaused`、`lagPaused`、`spare` はここではもう仮定しません。数えるフレームはポーズでない状態で終わるフレームで、4 バイトは `keep.clean` のガードに入っています（[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md)）。
* `state`（いまは `OnFrames` のフィールドで、触るまでのどのフレームでも。前は `Moves.state` で、`T` までの clean なフレームだけ）: 残るのは `Player_State` ∈ {0, 1, 2} とジャンプ台なしです。これらは地図と物のコードが書きます（ジャンプ台に乗ったときのジャンプ台、当たり判定のルーチンの `Player_State`）。操作中のフレームの歩きは地図も物も知らないので、これらを保つことは示せません。タイルについてのどの条件がこれらを出すか、それがなぜ小さくないかは [上](#プレイヤーの状態とジャンプ台証明していない) にあります。`AreaType`、`SwimmingFlag`、`PlayerChangeSizeFlag` は証明（`OnFrames.areaAll`）、`PrevA` も証明です（`OnFrames.prevAll`）。
* `After`、いまは `AfterP`: スクロールの処理で右へ動くフレームの位置。速さが変わらなければ位置も変わらず、速さが 0 で終わるなら、位置は移動の 1 ピクセル後ろか、フレームの始まりから 1 ピクセル以内で終わります。向きと当たり判定のビットはもうここでは求めません: 定理です（[上](#スクロールの処理からあと-向きサブ速さ当たり判定のビット)）。サブ速さ（`After.f`）と、そこで左へ動くか止まっているフレームでの `coll` は `collide` から出ます（`After.of`）。`storedQ` はもう仮定しません（[上](#スクロールの処理での覚えている速さ)）。
* `faceJ`: 1〜8 フレーム目で、速さ 0 とサブ速さ 0 で終わるフレームの終わりの向きは、スクロールの処理のもの。これらのフレームは `hstep` のとおりでなければなりません（`J` より前に当たりはない）。なのでここでは当たりでは足りません。そういうフレームでは彼は止まっています。よじ登れるタイルが向きを変えたかどうかを、歩きは知りません。
* `spareE`、`spareC`、`spareV` はここではもう仮定しません。どれも `keep.cleanE` のガード `guardE` に入っています（`spareE` は第 10 回、`spareC` は第 13 回、`spareV` は第 14 回）。この回から `guardE` は向きとサブ速さ（`FrameKeep.faceE`）、プレイヤーの状態と縦の力（`FrameKeep.stateE`）も守ります。
* `vAfter`: 1〜8 フレーム目で、スクロールの処理からあとが縦のバイトのうち 5 つ（`vHard`: 高さ、高さの端数、縦の速さ、端数のカウンタ、状態）を変えないこと。ルーチンが `vstep` のとおりなのは証明（`vert_of`）、その前の部分も証明（`vBefore`）、そのあとの 5 つのバイトも証明（`OnFrames.kAt`: 下向きの縦の力、ジャンプの始まりの高さ、ジャンプを止める値、A。`OnFrames.vfAt`: 縦の力）です。残りの 5 つには歩きだけでは足りません（[上](#スクロールの処理からあと-縦の-4-つのバイト)）: そのうち 4 つはスクロールの処理の前に添字で書かれるので `guardE` では守れません。地面の上では当たり判定のルーチンが `Player_State` を 2 にして、また着地させます。そして歩きは地図も物体（踏みつけ、リフト、ジャンプ台、ブロック）も知りません。
* [操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md) の `keep.ends`、`keep.clean` と定理 `keep.start`: フレームは同じなので、`ends` はここのフィールドではなくなりました。
* `box`: 1〜8 フレーム目で、当たり判定が操作のときの機械と同じ結果になること。
* `reads` はなくなりました。`fr` は機械の上の定義（`frOf`）で、触る前の各フレームが `TopSpeed.Frame` であることは証明です（[上](#機械から読むフレーム)）。残るのは 1 つのフレームか 1 つの機械の条件です:
  * `collide`: 触る前の各フレームで、当たり判定のルーチンとフレームの残りが位置にすることと、速さ 0 とサブ速さ 0 で終わるフレームでサブ速さにすること（`CollideS`）。`After` と同じフレームの部分の文ですが、clean なフレームだけでなく、どのフレームでもです。敵の処理もそこで動きます。速さの部分は証明です（`OnFrames.collideAt`）。ほかのどのフレームのサブ速さも証明です（`FaceKeep.keepZ_end`）。速さ 0 とサブ速さ 0 で終わるフレームでは、0 でなかったサブ速さをよじ登りのルーチンが 0 にしたのかどうかを、歩きは区別できません。`TopSpeed.Frame` はどのフレームでも `f' = f₂` を求めるので、これは残ります。位置は、敵の移動、横に動く台、当たり判定のルーチンの押し、画面の端で歩きが失敗します（[上](#スクロールの処理からあと-速さ)）。
  * どのフレームでもの `state`（上）。
* `chg.time₂`、`chg.ctlFirst₂`、定理 `Run.atCtl`。

**ファイル.** `Theorems/SurfaceFrames.lean`（`frOf`、`OnFrames.reads`、`OnFrames.collAll`）、`Theorems/SurfaceRead.lean`（`CollideE`、`read_move`、`frame_readE`、`frameE`、`frameH`）、`Theorems/CtrlKeep.lean`、`Theorems/PrevKeep.lean`（`prev_end`）、`Theorems/AfterKeep.lean`（`keepH`、`subs_once`）、`Theorems/CollKeep.lean`（`splitXAt`、`walkKX`、`collCheck`、`coll_end`、`cleanC_of`、`spareC_of`）、`Theorems/CollideKeep.lean`（`rkOff`、`walkKV`、`vCheck`、`endKV`、`speed_end`、`cleanV_of`、`spareV_of`）、`Theorems/VertKeep.lean`（`kI`、`kCheck`、`keep_end`）、`Theorems/FaceKeep.lean`（`zI`、`zCheck`、`keepZ_end`、`splitYAt`、`bCheck`、`bits_end`、`vfC`、`vfCheck`、`vf_end`、`cleanZ_of`、`cleanB_of`、`cleanVF_of`）、`Theorems/SurfaceLate.lean`（`sum_ge_late`、`level_ge_of_late`）、`Theorems/VertModel.lean`、`Theorems/FrameModel.lean`（`move_masked`、`trace_inFrame`、`stored_path`）、`Theorems/FrameWalk.lean`（`InFrame`）、`Theorems/SurfaceRun.lean`（`far`、`Statement.fric`）、非公開の `Proof/SurfaceFrames.lean`（`side_start`）、`Proof/PoleJoin.lean`（`pole_numbers`。`ctrlCheck`、`afterCheck`、`prevCheck`、`hCheck`、`storedOK`、`collCheckAll`、`vCheck`、`kCheck`、`zCheck`、`bCheck`、`vfCheck` を含む。`pole_far_count`）、`Proof/SurfaceRun.lean`（`surface_run`。`top_frictionCheck` を使う）。

**再現.**
```
.lake/build/bin/smbrta surface-frames-check FM2 200    # 上の表、CPU で約 9 分
.lake/build/bin/smbrta surface-read-check FM2 200      # 機械から読むフレーム、CPU で約 2 分
.lake/build/bin/smbrta vert-model-check                # vertOK とその各場合、約 0.1 秒
.lake/build/bin/smbrta mask-model-check                # maskOK とその部分、約 0.1 秒
.lake/build/bin/smbrta ctrl-keep-check                 # プレイヤーのルーチンまでの歩き: 25 バイトのそれぞれとポーズのビット、約 4 秒
.lake/build/bin/smbrta ctrl-after-check size           # 切れ目からの歩き（afterCheck）、約 20 秒。`pause` と `area` は見るバイトが少ない
.lake/build/bin/smbrta ctrl-prev-check                 # 第 8 回の、書き込みで切らない PrevA の探索（証明には入らない）、約 10 秒。exit 1（26 のフレームの終わりで失敗）
.lake/build/bin/smbrta prev-why none|cut                # 同じ探索で、失敗するフレームの終わりへの道を出す。cut は noStore の書き込みで切る: 失敗 0
.lake/build/bin/smbrta prev-check                       # prevCheck、約 3 秒
.lake/build/bin/smbrta after-keep-check                 # AfterKeep の探索と hCheck、約 4 秒
.lake/build/bin/smbrta after-bytes guard|prot           # 横のバイトのそれぞれの 2 つ目の探索: guard は keep.cleanF だけ、prot はバイトも守る
.lake/build/bin/smbrta after-real FM2 100               # 本物のフレームで SpareE、PrevOK、keepH、storedQ、After、約 80 秒
.lake/build/bin/smbrta stored-check                     # storedOK とその部分、約 0.4 秒
.lake/build/bin/smbrta spring-cut-check                 # ジャンプ台のバイトを見て、その書き込みで止める切れ目からの歩き（証明には入らない）、約 1 秒
.lake/build/bin/smbrta spring-real FM2 100              # 本物のフレームでのジャンプ台のバイトと状態の書き込み、約 80 秒
.lake/build/bin/smbrta coll-cut-check                   # 第 11 回の、当たり判定のビットを見る歩き（証明には入らない）、約 1.4 秒。exit 1（失敗 4）
.lake/build/bin/smbrta coll-key-check 0                 # 同じもので、バイト 0 を守りキーに入れる（証明には入らない）、約 9 分。exit 1
.lake/build/bin/smbrta coll-split-check                 # X を分ける探索と collCheck、約 9 秒
.lake/build/bin/smbrta coll-real FM2 200                # 本物のフレームで SpareC と当たり判定のビット、約 2 分
.lake/build/bin/smbrta keep-frames-check FM2 100        # 本物のフレームで guardE の CleanK（当たり判定のビット、速さ、vertE も）、触るフレームも、約 4 分
.lake/build/bin/smbrta collide-keep-check               # 速さの歩きの探索と vCheck、サブ速さの試み、約 5 秒。exit 0
.lake/build/bin/smbrta collide-real FM2 200             # 本物のフレームで SpareV、スクロールの処理からあとの速さ、サブ速さ、向き、当たり判定のビット、CollideS、AfterP、約 7 分
.lake/build/bin/smbrta face-keep-check                  # FaceKeep の歩きの探索、zCheck、bCheck、vfCheck、約 12 秒。終わりを「追っている」だけにした向きと、ジャンプ台のバイトで見る縦の力も（証明の一部ではない）
.lake/build/bin/smbrta face-keep-check ADDR             # 同じもので、ジャンプ台のバイトで見る縦の力は RAM のバイト ADDR も守る（ジャンプ台のタイマー: 失敗 0）
.lake/build/bin/smbrta pos-after-real FM2 200           # 本物のフレームで、スクロールの処理からあとに位置を変える命令と、変わる量、約 7 分
.lake/build/bin/smbrta vert-after-bytes prot            # スクロールの処理からあとの縦のバイトそれぞれの探索、ジャンプ台つきの縦の力、kCheck。約 6 秒。exit 1（vHard のバイトと、終わりを「追っている」だけにした縦の力）
.lake/build/bin/smbrta vert-after-bytes guard           # 同じもので、バイトを守らない: 約 95 か所で失う。exit 1
.lake/build/bin/smbrta vert-after-real FM2 400          # 本物の 1〜8 フレーム目で vAfter: スクロールの処理での場合分け、そのあとの変化とその順。約 30 秒。exit 0
```
