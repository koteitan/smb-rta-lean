[← Back](README-ja.md) | [English](a-5-7-OpenJump.md) | [Japanese](a-5-7-OpenJump-ja.md)

# 出だしのジャンプ

**主張.** 出だしの縦のモデルのジャンプは、地面から、どのフレームで A を押しても押さなくても、跳ぶときの速さの 2 つの測った長さのあいだで、地面の高さに、縦の速さ
なしで着地します。最初の `N` 個の数えるフレーム（`N = 32`）で、空中かジャンプを読む数えるフレームはこのモデルの 1 歩なので（[本物のフレームの上の縦のモデル](a-5-7-2-OpenAir-ja.md)、
前のフィールド `vert`）、ジャンプの長さ（前のフィールド `jump`）と着地のあとの地面の高さ（前のフィールド `ground`）は定理です。ジャンプは数えるフレーム
`H = min(N + 1, E)` までしか追いません。

`fm(t)` は数えるフレーム `t` が始まるときの機械です。`VS(m)` は `vstep` の縦のバイトです: 高さ `y`、その端数、縦の速さ `vy`、端数のカウンタ、2 つの力、
ジャンプの始まりの高さ、プレイヤーの状態 `st`、前のフレームの A。`hi(m)` は高さの上位バイト、`abs(m)` は覚えている速さ、`a(t)` はプレイヤーのルーチンが読む
数えるフレーム `t` の A、`y₀` は `m₀` の高さ、`S` はプレイヤーのルーチンのスタックポインタです。`vstepV` は機械 `VertModel.vmach` の上の `vstep` です（パート c）。
`flat(t) := st(fm t) = 0 ∧ ¬jump(in t)` です。`L(v) = (L_tap, L_hold)` は速さ `v` の `Opening.jumpLens` の長さです。

```
land(s)        :=  st(s) ≠ 0 ∧ vy(s) ≥ 0 ∧ y(s) ≥ y₀  なら  s の y = y₀、vy = 0、端数 0、st = 0   でなければ  s
vstepO(s, a, b) :=  land(vstepV(s, a, b))
ground0        :=  y = y₀、ほかのバイトは 0、前のフレームの A は押していない

arcOK          :  空中:  k < L_hold、 32 ≤ y < y₀;   着地:  L_tap ≤ k ≤ L_hold、 y = y₀、 vy = 0、 端数 0、
                  land の前の高さは [y₀, y₀ + LandDepth) の中;   両方:  1 歩のあとの上位バイト（vstep の機械の上）は 1
arcCheck       :  跳ぶ状態  vstepO(ground0, A, v)、 v ∈ [0, top]  から 80 フレーム以内に着くどの状態も arcOK;  L_tap ≤ L_hold ≤ 80
next_bound     :  着く状態で空中なら:  次の land の前の高さ < y₀ + LandDepth  かつ 1 歩のあとの上位バイト 1（どちらの A でも）
lands_by       :  arcCheck,  v ≤ top,  u(1) = vstepO(ground0, A, v),  ∀ e ∈ [1, h):  u(1), …, u(e) が空中,  P(e),  次の上限  →
                     P(e + 1)  ∧  u(e + 1) = vstepO(u(e), a(e), 0)
                  →   (∃ n ≤ h,  L_tap(v) ≤ n ≤ L_hold(v),  u(1), …, u(n − 1) は空中,  st(u(n)) = 0,  y(u(n)) = y₀,  vy(u(n)) = 0,  端数 0,  P(n))
                      ∨  (u(1), …, u(h) が空中  ∧  h < L_hold(v))

Real.jumpV     :  確認,  VertOK,  t ∈ [1, N],  t < E,  Held(fm t),  |v(fm t)| ≤ top,  st(fm t) = 0,  GroundAt(fm t),  jump(in t)
                  →   (∃ n,  t + n ≤ H,  L_tap ≤ n ≤ L_hold,  1 ≤ d < n で st(fm(t + d)) ≠ 0,  st(fm(t + n)) = 0,  GroundAt(fm(t + n)))
                      ∨  (t + d ≤ H で st(fm(t + d)) ≠ 0  ∧  H − t < L_hold)                                          （前のフィールド jump）
Real.ground_all : 確認,  Real,  各数えるフレームで Held、StSpring、|v| ≤ top,  st(fm 1) = 0,  GroundAt(fm 1)
                  →   ∀ t ∈ [1, N],  t < E,  st(fm t) = 0  →  GroundAt(fm t)                                       （前のフィールド ground）
Run.pipeSpeed  :  確認,  1 ≤ E   →   ∀ t ∈ [1, E],  |v(fm t)| ≤ top
```

`P(e)` はジャンプに沿って運びます: 本物のフレームでは高さの上位バイト 1 と止める値の関係です。`H = min(N + 1, E)` は見る範囲の端です: `N` までのモデルの
歩みはそのあとのフレームを要りません。ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。`#print axioms route_1_1` に `sorryAx`
はありません。

Lean: `Theorems/OpenJump.lean`（`land`、`vstepO`、`hiAfter`、`arcCheck`、`openJumpCheck`、`next_bound`、`start_bound`、`lands_by`）。`Theorems/OpenFrames.lean` の
`Real.jumpV`、`Real.ground_all`、`last_ground`、`aOf`、`airT`、`Checks.jumps`、`Checks.top16`。`Theorems/Route.lean` の `Run.pipeSpeed`。非公開の
`Proof/OpenJump.lean`（`open_jump_check`）。

## しくみ

* **モデル.** 跳ぶときルーチンは縦のバイトを速さの組から書き直します（`InitJS`: `|v|` の 5 つの組）。なので跳ぶところは `ground0` から始まります。空中では
  `vstep` は覚えている速さを 0 にして移動のルーチンを動かします: 空中のルーチンが覚えている速さを読むのは横の部分だけです（`VertAir`、パート c）。出だしの平らな
  地面では、当たり判定のルーチンは空中で着地のほかに何もしません: `land`。
* **探索.** 状態は縦の状態、フレームの数、2 つの長さです。跳ぶ状態（41 の速さで 3 つ）から、空中の各フレームで A によって分かれます。着地した状態に次は
  ありません。`arcCheck` は 80 までの各層のどの状態にも `arcOK` を求めます（`Cert.checkPrunedS`）。
* **着地.** `lands_by` は列 `u` を弧の上で追います。空中ではフレームの数は `L_hold` より小さく、次の弧の `arcOK` がモデルの次の高さを抑えます
  （`next_bound`）。本物のフレームの 1 歩はこれを要ります。最初に地面の上になるフレームは `L_hold` までに来て、そこで `arcOK` が `L_tap ≤ n` と地面の高さを
  出します。`h` までに来なければ、`h` までのフレームは空中で `h < L_hold` です。
* **本物のフレームで.** `Real.jumpV` は `u(e) = VS(fm(t + e))` とし、各本物のフレームの縦のモデル（`Real.vertOK`、[本物のフレームの上の縦のモデル](a-5-7-2-OpenAir-ja.md)）
  を見る範囲の端まで使います。高さの上位バイトと止める値の関係は `P` として運びます。`Real.ground_all` は着地の場合を `Real.jumpV` から出します: 着地の前に地面の
  上にあった最後の数えるフレームは跳ぶフレームです。ジャンプのない地面の上のフレームは地面の上に残るからです（`Real.flat`）。跳ぶときの速さは最高速以下です
  （`Run.pipeSpeed`）。モデルの空中に残るフレームの数え方（`airT`）は、`H` までに着地しないジャンプに `max(L_tap − 1, H − t − 1)` フレームを与えます。2 つの長さの
  あいだです。

| | 数 |
|---|---|
| 跳ぶ状態 | 3（`|v|` 0〜15: 長さ 21〜53、16〜24: 24〜58、25〜40: 21〜57） |
| 探索の状態 | 4,765。いちばん高いところは `y = 93` |
| モデルの着地 | どの組でも、ちょうど `L_tap` から `L_hold` まで |
| `openJumpCheck` | ネイティブで 1.2 秒（各歩のあとの上位バイトつき） |

## 本物のフレームでの確認

`open-real-check FM2 300` は、`N` までの空中かジャンプを読むどの数えるフレームでもモデルの 1 歩（`VStep`）を確かめます（数は
[本物のフレームの上の縦のモデル](a-5-7-2-OpenAir-ja.md) を見てください）。プログラムでは、きびしくした `arcOK` が 4,765 のどの状態でも成り立ちます。

## 仮定（Lean で証明していないもの）

* **もう仮定でないもの**: `vert`（いまは `Real.vertOK`）、`jump`、着地のあとの `ground`。

**ファイル.** `Theorems/OpenJump.lean`、`Theorems/OpenFrames.lean`、`Theorems/Route.lean`、非公開の `Proof/OpenJump.lean`。

**再現.**
```
.lake/build/bin/smbrta open-jump-check                  # モデルのジャンプの探索（約 5 秒）
.lake/build/bin/smbrta open-real-check FM2 300          # 本物のフレームでの Real のフィールドとモデルの 1 歩（約 1.5 分）
```
