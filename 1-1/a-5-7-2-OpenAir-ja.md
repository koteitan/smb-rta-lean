[← Back](README-ja.md) | [English](a-5-7-2-OpenAir.md) | [Japanese](a-5-7-2-OpenAir-ja.md)

# 本物のフレームの上の縦のモデル

**主張.** 最初の `N` 個の数えるフレーム（`N = 32`、入る `E` より前）のうち、跳ぶフレームか空中のフレームのあとの数えるフレームの縦のバイトは、出だしの縦のモデル
`vstepO` の 1 歩です（[出だしのジャンプ](a-5-7-OpenJump-ja.md)）。これは `OpenFrames.Real` のフィールド `vert` でした。いまは 1 つのフレームとその命令の条件からの
定理です（`Real.vertOK`）。また数えるフレーム `N` より後ではもう求めません: モデルは空中に残るフレームを数えるフレーム `H = min(N + 1, E)` までしか要りません。

`fm(t)` は数えるフレーム `t` が始まるときの機械、`R` はプレイヤーのルーチンに初めて着いたときの機械（`n₀ = arrAt`）、`Q` はスクロールの処理（`PlayerSubs`）、
`cE` は当たりのルーチン、`cR` はその戻り、`end` はフレームの終わりです。`VS(m)` は `vstep` のバイト（高さ `y`、その端数、縦の速さ `vy`、端数のカウンタ、2 つの力、
ジャンプの始まりの高さ、状態 `st`、A）、`hi(m)` は高さの上位バイト、`abs(m)` は覚えている速さ、`a(t)` はプレイヤーのルーチンが読むフレームの A、`y₀` は地面の高さ、
`d = LandDepth`、`top` は最高速です。`vstepV`、`vRun` は機械 `VertModel.vmach` の上の `vstep` と、移動のルーチンのあとのその機械です。

```
Halt(m)    :=  st(m) = 1  →  DiffToHaltJump(m) = 1
PrevOK(m)  :=  前のフレームの A と B の bit 7 = A と B の bit 7
r(t)       :=  vstepV(VS(fm t), a(t), 0)
VPre(t)    :=  (st(fm t) = 0  →  jump(t) ∧ GroundAt(fm t) ∧ abs(fm t) ≤ top)
               ∧ (st(fm t) ≠ 0  →  hi(fm t) = 1 ∧ Halt(fm t) ∧ y(r(t)) < y₀ + d ∧ hi(vRun) = 1)
VStep(t)   :=  hi(fm(t + 1)) = 1  ∧  Halt(fm(t + 1))
               ∧ (st(fm t) = 0  →  VS(fm(t + 1)) = vstepO(ground0, A, abs(fm t)))
               ∧ (st(fm t) ≠ 0  →  VS(fm(t + 1)) = land(r(t)))

Real.vertOK   :  確認,  Real,  各数えるフレームで Held と StSpring,  PrevOK(fm 1)
                 →   ∀ t ∈ [1, N],  t < E,  VPre(t)  →  VStep(t)
Real.prevAll  :  確認,  Real,  Held,  PrevOK(fm 1)   →   ∀ t ∈ [1, N + 1],  t ≤ E,  PrevOK(fm t)
Real.jumpV    :  確認,  VertOK,  t ≤ N、t < E で跳ぶ
                 →   (∃ n,  t + n ≤ H,  L_tap ≤ n ≤ L_hold,  t + 1 から t + n − 1 まで空中,  GroundAt(fm(t + n)))
                     ∨  (t + 1 から H まで空中  ∧  H − t < L_hold)
air_real      :  st(m) ∈ {1, 2},  Halt(m),  当たりの旗 0,  各命令で CleanK と RdOK1
                 →   フレームは R から Q に一度だけ k₁ で着き、そのあと k₂ で cR に着き、
                     Ok1(k₁)  →  VS(k₂) = land(VS(k₁)) ∧ hi(k₂) = 1 ∧ Halt(k₂)
                     Ok1(m) := y(m) < y₀ + d ∧ hi(m) = 1 ∧ st(m) ∈ {1, 2}
take_real     :  y₀ で abs(m) = u ≤ top で跳ぶ   →   初めての cR で:  VS = vstepO(ground0, A, u),  hi = 1,  DiffToHaltJump = 1
vert_airH     :  上位バイトつきの vert_air（パート c）:  hi(R) = 1  →  hi(Q) = hi(vRun)
```

`land` は `OpenJump.land` です。`H` は見る範囲の端です。ROM を使わない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/OpenAir.lean`（相、`piecesQ`、`zoneA`、`okA`、`startsA`、`airCheck`）、`Theorems/OpenAirFrame.lean`（`PhiA`、`phi_step`、`split_cover`、
`piece_facts`、`walk_frame`、`air_real`、`take_real`、`airAll`、`AfterVS`）、`Theorems/OpenWalk.lean`（`walkP`、`frame_of_walkP`）、`Theorems/OpenVert.lean`
（`vert_airH`、`vertAirHOK`）、`Theorems/OpenFrames.lean`（`VPre`、`VStep`、`VertOK`、`Real.vertOK`、`Real.prevAll`、`airT`）; 非公開の `Proof/OpenAir.lean`
（`open_air_check`、`open_vert_check`）。

## しくみ

**跳ぶフレーム.** プレイヤーのルーチンで、歩きは地面（`y₀`、上位バイト 1、縦の速さなし）、A を押していて前のフレームでは押していないこと、覚えている速さ `u` を
知っています。`u ≤ top` のそれぞれに 1 つの始まりがあります。ジャンプの始まりがほかの縦のバイトを書くので、歩きは当たりのルーチンの戻りまでどの縦のバイトも
知っていて、そこでそれがモデルの跳び方であることを確かめます（`vsK`）。

**空中のフレーム.** 移動のルーチンは、歩きの知らない値から縦のバイトを変えます。なので `Q` までは 2 つの機械の歩きで `vstep` に結びます（パート c の
`VertAir.vert_air` に上位バイトを足したもの: `OpenVert.vert_airH`）。`Q` からは 1 つの機械の歩き（`OpenWalk.walkP`、相つきの `OpenFlat` の歩き）がフレームの
終わりまで追います。相（`AS.log`）:

| 相 | どこから | 各ステップに求めること | 歩きの外の事実（`PhiA`） |
|---|---|---|---|
| `pre` | プレイヤーのルーチン | | まだ `Q` に着いていない |
| `q1`, `q` | `Q` | `pAll` の 11 バイトを書かない、2 回目の `Q` がない | `pAll` のバイトは `Q` のときのもの |
| `k1`, `k` | `cE`: `y₀` より上のちょうどの高さ、または地面の近くで上昇中 | 同じ | 同じで、`Q` で着地しない |
| `l1`, `l` | `cE`: 地面の近くで落下中、状態 1 か 2 | `pRest`（7 バイト）を書かない | `pRest` は `Q` のとおり、`Q` で着地する |
| `n1`, `n` | `cE`: 残り | 2 回目の `Q` がない | `Q` で `Ok1` が偽 |
| `aft` | `cR`: `k`（止める値の関係を知る）、`l`（`y₀` に着地し止める値の関係を知る）、`n` | `Q` がない | `Ok1(Q) → VS(cR) = land(VS(Q))`、`hi(cR) = 1`、`Halt(cR)` |
| `tk u`, `tkd` | 速さ `u` で跳ぶ; `cR` で `vsK` | | `VS(cR) = vstepO(ground0, A, u)` |

`cE` で相 `q` の状態は、ちょうどの高さ（`y₀ + d` より上、上位バイト 1）で分け、地面の近くでは縦の速さの bit 7 と状態でも分けます（`piecesQ`）。最初のブロックの
バッファは行ごとに 2 つのタイルしかないので、高さを知れば当たりのルーチンのどの読みも分かります。ステップが「書かない」のは `StepWrites.keepOK` です
（[1 ステップの補題](d-3-4-1-StepWrites-ja.md)）。事実 `PhiA` は各ステップで続き（`phi_step`）、`OpenWalk.frame_of_walkP` でフレームの終わりでも成り立ちます。
歩きは、フレームがプレイヤーのルーチンのあと `Q` に一度だけ着くことを求めます。なので `vert_airH` の着く時は歩きのものと同じで、`VS(Q)` はモデルの `r(t)` です。
`VPre` が `Q` での `Ok1` を与えます: モデルの 1 歩の高さは `y₀ + d` より上、1 歩のあとの上位バイトは 1 です（`OpenJump` の探索が両方を求めます）。

**当たりの旗.** 当たりのルーチンは、旗 `DisableCollisionDet` が 0 でないと何もしません（書くのはつるの入り口だけです）。RAM の番号は ROM から読みます（ルーチンの
最初の load の operand）。[ブロックのバッファ](a-5-4-3-3-3-OpenMap-ja.md) がいまはこれもどのフレームでも 0 に保ち、`CtrlKeep` の歩きがプレイヤーのルーチンまで
追います。

**戻りのあと.** `vsA` のバイト（11: 縦のバイト、上位バイト、状態、A と B、止める値）は変わりません: フィールド `afterV`、仮定（前と同じで、バイトが多い）。
数えないフレームはこれを保ちます: [LagFrames](a-5-5-3-LagFrames-ja.md) が 7 バイト多く追います。

**2 つの関係.** 止める値の関係は各ジャンプに沿って運びます: 跳ぶとき歩きは止める値 1 を知り、空中では歩きが `cR` で確かめます。`PrevOK` はパート e の歩き
（`GuardE.prev_endE`）で各数えるフレームで成り立ちます: `guardE` の `CleanK` と、ルーチン、モード、タスクへの番地での書き込みがないこと（守るバイトが 5 つ増えた
フィールド `cleanK` と新しいフィールド `noStore`）、それに数えるフレーム 1 での `PrevOK`（操作できる時の状態のタイトルの確認が A と B と前のフレームの A と B も
求めます、`StartRun.stI`）を求めます。

**見る範囲.** `H` までに着地しないジャンプには、空中のフレームを `max(L_tap − 1, H − t − 1)` 与えます（`airT`）。`arcOK` が `H − t < L_hold` を与えます。`N` までの
モデルの歩みにはそれ以上は要りません。

| ROM の確認 | 数 | ネイティブの時間 |
|---|---|---|
| `airCheck`: 探索 | 探索 506,135 回、失敗 0、表 95,459 状態 | 40 s |
| `airCheck`: 表と 129 の始まり（3 つの切れ目 × 43）の歩き | | 4.3 s |
| `vertAirHOK`（上位バイトつきの `vert_air` の歩き） | 最初の部分 4,608、場合 16、最後の部分 | 0.2 s |
| 当たりの旗のプレイヤーのルーチンまでの歩き | | 0.3 s |
| 上位バイトつきの `openJumpCheck` | 4,765 状態 | 1.2 s |

`airCheck` は数秒よりずっと長くかかります: 探索が確認の中にあります（`native_decide` が実行します）。自分の非公開のファイル `Proof/OpenAir.lean` にあります。

## 本物のフレームで確かめた

`open-real-check FM2 300` は、`N` までの各数えるフレームで `Real` のフィールド（`guardE` の `cleanK`、`noStore`、11 バイトの `afterV`、`map`、`after`）、
証明がフレームの始まりで出すもの（`PrevOK`、止める値の関係、当たりの旗 0）、空中か跳ぶフレームで 1 歩 `VStep` を確かめます:

| 回 | 数えるフレーム | 空中か跳ぶ | 跳び始め | 条件を満たさないフレーム |
|---|---|---|---|---|
| ムービー（HappyLee）、1 回 | 32 | 29 | 2 | 0 |
| 操作できる時からの自分の乱数の入力、300 回 | 9,600 | 8,069 | 528 | 0 |
| 最初のフレームでポーズする自分の回、60 回 | 1,856 | 1,624 | 116 | 0 |

`open-map-check FM2 30` は `map`（いまは当たりの旗も）を確かめます: 91 回、9,997 フレーム、24,433,366 命令、`MapOK` でないもの 0。

## 仮定（Lean で示していない）

* **もう仮定しない**: `vert`。
* **新しい**: `noStore`（数えるフレームのどの命令もルーチン、モード、タスクに番地で書かない）。
* **広げた**: `cleanK` は `guardE` の `CleanK` を求めます（守るバイトが 5 つ増える: A と B、前のフレームの A と B、動く向き、走る速さ、覚えている速さ）; `afterV`
  は 11 バイトを求めます（前は 4）; `map`（`MapOK`）は当たりの旗も守ります。

**ファイル.** `Theorems/OpenAir.lean`、`Theorems/OpenAirFrame.lean`、`Theorems/OpenWalk.lean`、`Theorems/OpenVert.lean`、`Theorems/OpenFrames.lean`、非公開の
`Proof/OpenAir.lean`。

**再現.**
```
.lake/build/bin/smbrta open-air-search all          # 歩きの探索と確認、ほかの確認（約 50 s）
.lake/build/bin/smbrta open-real-check FM2 300      # 本物のフレームの上の Real の条件
```
