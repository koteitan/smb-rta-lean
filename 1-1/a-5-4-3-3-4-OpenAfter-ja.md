[← Back](README-ja.md) | [English](a-5-4-3-3-4-OpenAfter.md) | [Japanese](a-5-4-3-3-4-OpenAfter-ja.md)

# スクロールの処理のあとと当たり判定のルーチンのあとの出だし

**主張.** 最初の 32 の数えるフレームの 2 つのフィールドが、前より少ないことを求めます。

* `after`（スクロールの処理からフレームの終わりまで）は、横の 8 つのバイト、覚えている速さ、当たりのビットを求めていました。いまは位置の 3 つのバイト、
  0 でない速さを 0 にしないこと、当たりのビットを求めます。向きとサブ速さは、フレームが速さ 0 とサブ速さ 0 で終わるときだけ求めます（17 回目。前は 5 つのバイト）。動く向き、走りの速さ、速さ、覚えている速さは定理です。
* `afterV`（当たり判定のルーチンから戻ったあと、フレームの終わりまで）は縦の 11 のバイトを求めていました。いまは 6 つです（17 回目。前は 7 つ）。下向きの縦の力、ジャンプの始まりの高さ、
  ジャンプを止める値、A と B、縦の力は定理です。
* 前の `after` は、数えるフレーム 32 で**本物の実行で偽**でした。新しい `after` は、フレーム 32 がレベルの左端で終わることを許します。

`fm(t)` は数えるフレーム `t` が始まるときの機械、`b(t)` はその終わりの機械、`tr(t, k)` はその `k` 命令あとの機械、`n₀(t)` はプレイヤーのルーチンに初めて来る命令です。
`Q` はスクロールの処理（`PlayerSubs`）、`cR` はプレイヤーのルーチンの中で当たり判定のルーチンから戻るところです。`v` は速さ、`ab` は覚えている速さ、`sub` はサブ速さ、`bits` は当たりのビット、
`hs` は横の状態、`P` は位置（1/256 px）です。`N = 32`、`E` は入るフレームです。

```
hRest          =  {Player_X_Position, Player_PageLoc, SprObject_X_MoveForce}
zeroRest       =  {Player_X_MoveForce, PlayerFacingDir}
AfterR(q, b)   :=  (∀ x ∈ hRest,  b[x] = q[x])  ∧  (v(b) = 0 → v(q) = 0)  ∧  bits(b) = FF
                   ∧  (v(b) = 0 ∧ sub(b) = 0  →  ∀ x ∈ zeroRest,  b[x] = q[x])
AtEdge(b)      :=  Player_PageLoc(b) = 0  ∧  Player_X_Position(b) = 0
after  (フィールド) :  t ∈ [1, N],  t < E,  k ≥ n₀(t),  pc(tr(t, k)) = Q   →   AfterR(tr(t, k), b(t))  ∨  (t = N ∧ AtEdge(b(t)))

vsR            =  {Player_Y_Position, Player_Y_HighPos, Player_Y_Speed, Player_Y_MoveForce, Player_YMF_Dummy, Player_State}
kI             =  {VerticalForceDown, JumpOrigin_Y_Position, DiffToHaltJump, A_B_Buttons}
retI           =  kI ∪ {VerticalForce}
afterV (フィールド) :  t ∈ [1, N],  t < E,  k ≥ n₀(t),  pc(tr(t, k)) = cR   →   ∀ x ∈ vsR,  b(t)[x] = tr(t, k)[x]

Real.frame_step :  Checks,  Real,  t ∈ [1, N],  t < E,  StartK(fm t),  Held(fm t),  st(fm t) ∈ {0, 1, 2},  ジャンプ台なし,  |v(fm t)| ≤ top
                   →   st(tr(t, n₀)) = st(fm t)
                       ∧ ( (hs(b t) = hstep(hs(fm t), in t)  ∧  (P(b t) − P(fm t) − 16·v(b t)) mod 2²⁴ = 0  ∧  Held(b t))
                           ∨ (t = N ∧ AtEdge(b t)) )
Real.afterVS    :  Checks,  Real,  t ∈ [1, N],  t < E,  Held(fm t)
                   →   ∀ k ≥ n₀(t),  pc(tr(t, k)) = cR  →  ∀ x ∈ vsR ∪ retI,  b(t)[x] = tr(t, k)[x]              （前のフィールド afterV）

OpenAfter.keep_at  :  ctrlCheck,  checkAt(v, q, bs),  StartK(m),  各命令が CleanK_F,  各 x ∈ bs について x も守るガードの CleanK,
                      ルーチン、モード、タスクへのアドレスでの書き込みなし,  AreaOK(v, m),  n₀ はプレイヤーのルーチンに初めて来る命令
                      →   ∀ k ≥ n₀,  pc(tr k) = q  →  ∀ x ∈ bs,  frame(m, i)[x] = tr(k)[x]
OpenAfter.keep_ret_all :  keep_at で  q = cR,  bs = retI,  各命令が CleanK_E（`keep_ret` は bs = kI のまま）
```

`Held(m)` は `ab(m) = |v(m)| ∧ bits(m) = FF ∧` エリアの 3 つのバイトです。`CleanK_E` は `FrameKeep.guardE` の `CleanK`、`CleanK_F` は `FrameKeep.guardF` の `CleanK` です。
ROM を使わない定理の公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/OpenAfter.lean`（`checkAt`、`retI`、`retCheck`、`keep_at`、`keep_ret_all`、`keep_ret`）、`Theorems/OpenFrames.lean`（`hRest`、`zeroRest`、`AfterR`、`Checks.zk`、`AtEdge`、`Real.frame_step`、
`Real.afterVS`、`OpenRunM.endB`）、`Theorems/OpenAirFrame.lean`（`vsR`、`AfterVR`）。非公開の `Proof/OpenAfter.lean`（`open_after_check`）。

## 前の `after` は本物の実行で偽だった

前のフィールドは、フレーム 1 から 32 のどれでも、スクロールの処理からあとで横のバイトが変わらないと言っていました。プログラム `open-left-real` は、
操作からの自分の入力で、位置がいちばん小さくなるものを探します（本物の機械の上のビーム探索、1 フレームに 10 の入力）。

| フレーム | フレームの終わりのいちばん小さい位置 | 前の `after` が偽のフレーム |
|---|---|---|
| 1 から 31 | フレーム 31 で 576（2.25 px） | 0 |
| 32 | 0（左端） | 624 |

走らせたフレームは全部で 22,100 です。

その 1 つは、A と B と左、左、A と左、左、左、A と B と左、… の 32 フレームです。フレーム 32 は `P = 576`、速さ −40 で始まります。移動で `P = −64` になります。
スクロールの処理のところでページは 255 です。スクロールの処理は、彼が画面の左端より左にいるのを見つけて、左端に置き、速さを 0 にします。フレームは `P = 192`、
速さ 0 で終わります。だから、フレームの終わりの位置、ページ、速さは、スクロールの処理のときのものではありません。

モデルも同じことを言います。31 フレームでは、どの入力も 9664 より左へ行きません（`P ≥ 576`）。32 フレームでは 10304 より左へ行きません（`P ≥ −64`）。
どちらの上限にも届きます（`open-left-check 31 9664` は真、`31 9600` は偽。`32 10304` は真、`32 10240` は偽）。フレーム 1 から 31 では、彼は左端から 2 px 以上
右にいます。だからそこでは端は彼を止めません。

そこで `after` は、フレーム `N` に 2 つめの場合を持ちます。フレームがレベルの左端で終わる場合です（`AtEdge`: ページ 0、ピクセル 0）。上の 624 フレームでは成り立ちます。
このときフレームはモデルの 1 歩ではありません。出だしの上限はじかに出ます。彼は 1 px より左にいて、操作のときの機械は左端から 1 px 以上離れています
（`Checks.left`、`m₀` の確認）。`OpenRunM.step` も同じ 2 つめの場合を持ちます。`OpenRunM.reachAll` はフレーム `N` の始まりまで進みます。`OpenRunM.endB` は
フレーム `N` を場合に分けます。1 つめの場合には、フィールド `page` がまだ要ります。

## しくみ: スクロールの処理のあと

パート e は、スクロールの処理からフレームの終わりまでの 3 つの歩きを証明しました。操作できる状態で始まるフレームで、各命令が `CleanK_E` を満たし、
ルーチン、モード、タスクへアドレスで書かないときです。出だしのフレームはこれを満たします（`cleanK` は `chg.upCleanU` から。書き込みがないことは
[OpenStore](a-5-4-3-3-5-OpenStore-ja.md)）。

* `GuardE.keepHE`: フレームの終わりの動く向き、走りの速さ、覚えている速さは、`Q` のときのものです。
* `CollideKeep.speed_end`: フレームの終わりの速さは、`Q` のときの速さか、0 です。`AfterR` は、`Q` で 0 でなければ 0 にならないと言います。だから `Q` のときの速さです。
* `FrameModel.stored_path`: `Q` で覚えている速さは `|v|` です。フレームが始まるときに、速さが最高速以下で、当たりのビットが 4 つの値のどれかであることを使います
  （`Held`、`Run.pipeSpeed`）。フレームはプレイヤーのルーチンのあとで `Q` に 1 回だけ来ます（`GuardE.subs_onceE`）。だから `stored_path` が着くところは、移動が着くところです。

`AfterR` の 3 つのバイトと、向きとサブ速さ（`FaceKeep.keepZ_end`。速さ 0 とサブ速さ 0 で終わるときは `AfterR`）と合わせると、フレームの終わりの横の 8 つのバイトは全部 `Q` のときのもので、フレームの終わりで `ab = |v|` です。これが前のフィールドの内容です。

## しくみ: 当たり判定のルーチンから戻ったあと

パート e の `VertKeep.keep_end` は、`kI` の 4 つのバイトを `Q` からフレームの終わりまで保ちます。`afterV` は、もっとあとの場所 `cR` でこれを求めます。
歩きが与えるのはフレームの終わりだけで、途中の命令ではありません。そこで `OpenAfter` は、`AfterKeep` の同じ 2 つの歩きを、`Q` の代わりに `cR` で走らせます（`checkAt`）。
プレイヤーのルーチンから `cR` に初めて来るまでの歩きと、そこからフレームの終わりまで 1 つのバイトを追う歩きです（そのバイトへの書き込みがあるか、`cR` にもう一度来ると
失敗します）。

先に試したことと、うまくいかなかった理由: `keep_end` の「途中のどの命令でも」という形。追うバイトを持たない状態は、そのバイトがどんな値でも機械を覆います。
するとフレームの終わりが 2 つの値を持つことになるので、途中のどの状態もバイトを追っています。けれども、状態が「バイトが 1 下がった」（`spent`）と言うことがあり、
抽象の命令 1 つずつについての補題がないと、これを除けません。

## ほかのバイトが残る理由

`open-after-search` は、バイトごとに、そのバイトを追って守りながら、`Q` から、または `cR` からフレームの終わりまで探索します。失敗は、そのバイトへアドレスで書く道です。

| バイト | `guardE` が守る | `Q` からの失敗する道 | `cR` から | `cR` のあとの書き込み |
|---|---|---|---|---|
| `Player_MovingDir`、`RunningSpeed`、`Player_XSpeedAbsolute` | はい | 0 | 0 | 証明済み（`keepHE`） |
| `Player_X_Speed` | はい | 17 | 13 | `KillPlayer`（10）、`ImpedePlayerMove`（3）。保つか 0、証明済み（`speed_end`） |
| `VerticalForceDown`、`JumpOrigin_Y_Position`、`DiffToHaltJump`、`A_B_Buttons` | はい | 0 | 0 | 証明済み（`keep_end`、`keep_ret`） |
| `Player_CollisionBits` | はい | 4 | 3 | `ImpedePlayerMove`（足場の横） |
| `SprObject_X_MoveForce` | はい | 25 | 25 | 移動のルーチンの書き込みで、添字が 0 かもしれないもの |
| `Player_X_Position` | いいえ | 34 | 30 | 移動のルーチン（25）、`PositionPlayerOnHPlat`（2）、`ImpedePlayerMove`（3） |
| `Player_PageLoc` | いいえ | 36 | 32 | 同じものと `ExecGameLoopback`（2） |
| `Player_X_MoveForce` | いいえ | 1 | 0 | なし（`cR` の前: `PutPlayerOnVine`） |
| `PlayerFacingDir` | いいえ | 2 | 0 | なし（`cR` の前: `FlagpoleCollision`、`PutPlayerOnVine`） |
| `Player_Y_Position` | いいえ | 11 | 10 | `PositionPlayerOnVPlat`（8）、ジャンプ台（2） |
| `Player_Y_HighPos` | いいえ | 8 | 8 | `PositionPlayerOnVPlat` |
| `Player_Y_Speed` | いいえ | 38 | 34 | 踏みつけ、はね返り、足場、ジャンプ台、`KillPlayer` |
| `Player_Y_MoveForce` | いいえ | 9 | 8 | `PositionPlayerOnVPlat` |
| `Player_State` | いいえ | 6 | 3 | `SetCollisionFlag`（足場） |
| `Player_YMF_Dummy`、`VerticalForce` | いいえ | 0、1 | 0、0 | なし |

* 位置、ページ、当たりのビット、高さ、縦の速さ、状態は、`cR` のあとで敵のコードが書きます（足場、踏みつけ、ジャンプ台）。歩きは敵などの物体を知りません。
  だからこれらは `after` と `afterV` に残ります。
* `Player_X_MoveForce`、`PlayerFacingDir`、`Player_YMF_Dummy`、`VerticalForce` には、`cR` のあとの書き込みがありません。けれども `guardE` がこれらを守らないので、
  添字やポインタを通した書き込みがあると、歩きはこれらを見失います。各命令についての新しい条件が要ります（`ImposeGravity` は `Q` の前に添字 0 で
  `Player_YMF_Dummy` を書きます）。やっていません。`guardE` と `chg.upCleanU` は、このラウンドではほかのパートのものです。

## 確認

| 確認 | 数 | ネイティブでの時間 |
|---|---|---|
| `OpenAfter.retCheck`（`cR` までの探索: 13,324 歩、そこでの状態 28。`cR` からの 4 つの探索: それぞれ 58,398 歩、表 3,723） | 失敗 0 | 2.3 秒（`Proof.OpenAfter` は 4.1 秒） |
| `AfterKeep.hCheck`、`CollideKeep.vCheck`、`FrameModel.storedOK`、`TopSpeed.frictionCheck` | パート e のもの（`pole_numbers`、`top_frictionCheck`） | 新しい時間なし |

## 本物のフレームで確かめた

`open-real-check FM2 300` は、数えるフレームごとに、新しい `after` と `afterV`、それに歩きと証明が言うことを確かめます。`keepHE`、`speed_end`、`keep_ret`、
`Q` とフレームの終わりの覚えている速さ、`AfterR` が成り立つときの横の 8 つのバイトです。

| 実行 | 数えるフレーム | 条件が偽のフレーム |
|---|---|---|
| TAS | 32 | 0 |
| 操作からの自分の入力（300） | 9,600 | 0 |
| 最初のフレームでポーズする自分の実行（60） | 1,856 | 0 |
| `open-left-real FM2 60`（左への探索） | 22,100 | 0（最後のフレームが左端で終わるもの 624） |

## 17 回目: 縦の力と、0 の場合だけの向きとサブ速さ

縦の力は、当たり判定のルーチンから戻ったところからフレームの終わりまで、歩きで追えます（`retI`、`keep_ret_all`）。`guardE` の `stateE` がすでに守っているので、ガードは増えません。向きとサブ速さは、part e の `FaceKeep.keepZ_end` が、フレームが速さ 0 とサブ速さ 0 で終わる場合を除いて与えます。前の `after` はこの 2 つを常に求めていたので、新しい条件は前の条件から出ます。新しい走りの仮定はありません。`Checks.zk` は既存の `SurfaceFrames.Numbers.zk` から出ます。

残りの縦の 6 つのバイトは、戻ったあとに直接の書き込みがあります。全バイトの探索（`open-after-search all`）での失敗は、高さ 10、その上位バイト 8、縦の速さ 34、縦の速さの端数 8、状態 3 です。状態は `guardE` が守っていても、番地での書き込みは止まりません。縦の力には失敗がありません。足の読みで高さを分けても、戻ったあとの敵や足場の書き込みは消せないので、大きな探索はしていません。

17 回目の確認は全部 exit 0 です: `open-real-check FM2 300`（ムービー、自分の入力 300 回、ポーズする 60 回で違反 0）、`open-left-real FM2 60`（22,100 フレームで失敗 0、フレーム 32 の左端 624）、`open-after-search all`、`open-air-search all`（空中の確認はネイティブで約 4.6 秒）。非公開の `Proof.OpenAfter` は約 2 秒です。

## 仮定（Lean で証明していないこと）

* `after`: `hRest` の 3 つのバイト、速さ 0 とサブ速さ 0 で終わるときの `zeroRest` の 2 つのバイト、速さを 0 にしないこと、当たりのビットが `FF`。またはフレーム `N` でレベルの左端。
* `afterV`: `vsR` の 6 つのバイト。
* `page`（前と同じ）。

**再現.**
```
.lake/build/bin/smbrta open-after-search all        # スクロールの処理からと、戻ったところからの、バイトごとの探索（8 秒）
.lake/build/bin/smbrta open-after-search check      # OpenAfter.retCheck
.lake/build/bin/smbrta open-left-real FM2 60        # 左への自分の入力の探索と Real の条件（1 分）
.lake/build/bin/smbrta open-real-check FM2 300      # 本物のフレームでの Real の条件
```
