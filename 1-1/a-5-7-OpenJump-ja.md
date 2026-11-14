[← Back](README-ja.md) | [English](a-5-7-OpenJump.md) | [Japanese](a-5-7-OpenJump-ja.md)

# 出だしのジャンプ

**主張.** 出だしの縦のモデルのジャンプは、地面から、どのフレームで A を押しても押さなくても、跳ぶときの速さの 2 つの測った長さのあいだで、地面の高さに、縦の速さ
なしで着地します。なので最初の `N` 個の数えるフレーム（`N = 32`）で、空中かジャンプを読む数えるフレームがこのモデルの 1 歩なら（新しいフィールド `vert`）、
ジャンプの長さ（前のフィールド `jump`）と着地のあとの地面の高さ（前のフィールド `ground`）は定理になります。

`fm(t)` は数えるフレーム `t` が始まるときの機械です。`VS(m)` は `vstep` の縦のバイトです: 高さ `y`、その端数、縦の速さ `vy`、端数のカウンタ、2 つの力、
ジャンプの始まりの高さ、プレイヤーの状態 `st`、前のフレームの A。`hi(m)` は高さの上位バイト、`abs(m)` は覚えている速さ、`a(t)` はプレイヤーのルーチンが読む
数えるフレーム `t` の A、`y₀` は `m₀` の高さ、`S` はプレイヤーのルーチンのスタックポインタです。`vstepV` は機械 `VertModel.vmach` の上の `vstep` です（パート c）。
`flat(t) := st(fm t) = 0 ∧ ¬jump(in t)` です。`L(v) = (L_tap, L_hold)` は速さ `v` の `Opening.jumpLens` の長さです。

```
land(s)        :=  st(s) ≠ 0 ∧ vy(s) ≥ 0 ∧ y(s) ≥ y₀  なら  s の y = y₀、vy = 0、端数 0、st = 0   でなければ  s
vstepO(s, a, b) :=  land(vstepV(s, a, b))
ground0        :=  y = y₀、ほかのバイトは 0、前のフレームの A は押していない

arcOK          :  空中:    k < L_hold、かつ  32 ≤ y < y₀  か  vy < 0
                  着地:    L_tap ≤ k ≤ L_hold、 y = y₀、 vy = 0、 端数 0、 land の前の高さは [y₀, y₀ + LandDepth) の中
arcCheck       :  跳ぶ状態  vstepO(ground0, A, v)、 v ∈ [0, top]  から 80 フレーム以内に着くどの状態も arcOK;  どの L_hold も 80 以下
lands          :  arcCheck,  v ≤ top,  u(1) = vstepO(ground0, A, v),  ∀ e ∈ [1, 80):  u(1), …, u(e) が空中  →  u(e + 1) = vstepO(u(e), a(e), 0)
                  →   ∃ n,  L_tap(v) ≤ n ≤ L_hold(v),  u(1), …, u(n − 1) は空中,  st(u(n)) = 0,  y(u(n)) = y₀,  vy(u(n)) = 0,  端数 0

フィールド vert :  ∀ t,  1 ≤ t < N + 80,  N < s ≤ t で st(fm s) ≠ 0,  ¬flat(t)   →   hi(fm(t + 1)) = 1  ∧
                  (st(fm t) = 0  →  VS(fm(t + 1)) = vstepO(ground0, A, abs(fm t)))  ∧
                  (st(fm t) ≠ 0  →  VS(fm(t + 1)) = vstepO(VS(fm t), a(t), 0))
Real.jumpV     :  確認,  Real,  t ∈ [1, N],  Held(fm t),  |v(fm t)| ≤ top,  st(fm t) = 0,  jump(in t)
                  →   ∃ n,  L_tap ≤ n ≤ L_hold,  1 ≤ d < n で st(fm(t + d)) ≠ 0,  st(fm(t + n)) = 0,  GroundAt(fm(t + n))      （前のフィールド jump）
Real.ground_all : 確認,  Real,  各数えるフレームで Held、StSpring、|v| ≤ top,  st(fm 1) = 0,  GroundAt(fm 1)
                  →   ∀ t ∈ [1, N],  t < E,  st(fm t) = 0  →  GroundAt(fm t)                                       （前のフィールド ground）
Run.pipeSpeed  :  確認,  1 ≤ E   →   ∀ t ∈ [1, E],  |v(fm t)| ≤ top
```

`vert` は `N` までの数えるフレームと、`N` のあとは数えるフレーム `N + 1` で空中にあるジャンプが続くあいだだけに求めます。そのあとのフレームは最初のブロックに
近づき、モデルはブロックを知りません。ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。`#print axioms route_1_1` に `sorryAx`
はありません。

Lean: `Theorems/OpenJump.lean`（`land`、`vstepO`、`arcCheck`、`openJumpCheck`、`lands`）。`Theorems/OpenFrames.lean` のフィールド `Real.vert`、`Real.jumpV`、
`Real.ground_all`、`last_ground`、`aOf`、`Checks.jumps`、`Checks.top16`。`Theorems/Route.lean` の `Run.pipeSpeed`。非公開の `Proof/OpenJump.lean`（`open_jump_check`）。

## しくみ

* **モデル.** 跳ぶときルーチンは縦のバイトを速さの組から書き直します（`InitJS`: `|v|` の 5 つの組）。なので跳ぶところは `ground0` から始まります。空中では
  `vstep` は覚えている速さを 0 にして移動のルーチンを動かします: 空中のルーチンが覚えている速さを読むのは横の部分だけです（`VertAir`、パート c）。出だしの平らな
  地面では、当たり判定のルーチンは空中で着地のほかに何もしません: `land`。
* **探索.** 状態は縦の状態、フレームの数、2 つの長さです。跳ぶ状態（41 の速さで 3 つ）から、空中の各フレームで A によって分かれます。着地した状態に次は
  ありません。`arcCheck` は 80 までの各層のどの状態にも `arcOK` を求めます（`Cert.checkPrunedS`）。
* **着地.** `lands` は列 `u` を弧の上で追います（`reach_arcs`）。空中ではフレームの数は `L_hold` より小さいので、最初に地面の上になるフレームは `L_hold` までに
  来ます。そこで `arcOK` が `L_tap ≤ n` と地面の高さを出します。
* **本物のフレームで.** `Real.jumpV` は `u(e) = VS(fm(t + e))` とし、各歩に `vert` を使います。着地のときの高さの上位バイトは、その前のフレームの `vert` から
  出ます。`Real.ground_all` は着地の場合を `Real.jumpV` から出すようになりました: 着地の前に地面の上にあった最後の数えるフレームは跳ぶフレームです。ジャンプの
  ない地面の上のフレームは地面の上に残るからです（`Real.flat`）。跳ぶときの速さは最高速以下です（`Run.pipeSpeed`、`PipeFrames.speed_of_reads` から）。

| | 数 |
|---|---|
| 跳ぶ状態 | 3（`|v|` 0〜15: 長さ 21〜53、16〜24: 24〜58、25〜40: 21〜57） |
| 探索の状態 | 4,765。いちばん高いところは `y = 93` |
| モデルの着地 | どの組でも、ちょうど `L_tap` から `L_hold` まで |
| `openJumpCheck` | ネイティブで 2.4 秒 |

## 本物のフレームでの確認

`open-real-check FM2 300` は、空中かジャンプを読むどの数えるフレームでも `vert` を確かめます。数えるフレーム `N` まで、そのあとは着地までです: TAS 42 フレーム、
自分の入力 11,839 フレーム、最初のフレームでポーズする走り 2,571 フレームで、失敗 0 です。この回の前の `jump` も同じ走りで成り立ちます（跳び始め 2 + 528 + 116）。

## 仮定（Lean で証明していないもの）

* **`vert`**（新しい）: 空中かジャンプを読む数えるフレームのあとの数えるフレームの縦のバイトは `vstepO` の 1 歩で、高さの上位バイトは 1。1 フレームごとの
  条件です。その部分は: スクロールの処理までの移動（跳ぶときは `VertModel.vert_model`、空中は `VertAir.vert_air`: プレイヤーのルーチンでの条件のもとで証明
  済み）、空中の当たり判定のルーチン（`land`: 証明していない）、当たり判定から戻ったあとのフレーム（`afterV` と同じ、ただし `VS` のすべてのバイト）、数えない
  フレーム（`lags_keepI` と同じ、そこにない `VS` のバイト）。これらを証明するのが次の段です。
* **もう仮定でないもの**: `jump`、着地のあとの `ground`。

**ファイル.** `Theorems/OpenJump.lean`、`Theorems/OpenFrames.lean`、`Theorems/Route.lean`、非公開の `Proof/OpenJump.lean`。

**再現.**
```
.lake/build/bin/smbrta open-jump-check                  # モデルのジャンプの探索（約 5 秒）
.lake/build/bin/smbrta open-real-check FM2 300          # 本物のフレームでの vert と Real のほかのフィールド（約 1.5 分）
```
