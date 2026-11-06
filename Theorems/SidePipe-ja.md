[← Back](../README-ja.md) | [English](SidePipe.md) | [Japanese](SidePipe-ja.md)

# 横の土管に入る

**主張.** マリオが横の土管に入るのは、地面に着地するか立っているフレームで、上昇中でなく、右を向いていて、右側が土管の口に入っているときだけです。空中では土管に止められます。
なので入るフレームは地面のフレームで、口の左端かそれより右にいて、かたまりからの落下が終わるより前には来ません。

`x₀` は右側が口に入る最初の `x`、`P₀` は口の左端の位置です。

```
rule(x, y, vy, 向き)  ⇔  0 ≤ vy  ∧  足が地面の着地の深さにある  ∧  向き = 右  ∧  x₀ ≤ x

enters_eq_rule    :  sideCheck → 範囲の全部の状態で enters = rule
ground_of_enters  :  sideCheck, enters → 地面にいる
mouth_of_enters   :  sideCheck, enters → x₀ ≤ x
no_enter_left     :  sideCheck, P < P₀ → 入らない
entry_after_jump  :  s ≤ N で P(s) < goal,  goal ≤ P(t + 1),  t + d ≤ E  →  N + d ≤ E
entry_after_step  :  s ≤ N で P(s) < goal,  goal ≤ P(t),  t + w ≤ E  →  N + 1 + w ≤ E
slow_short        :  P(T + air) ≤ B + c·(air + 1),  B + c·(air + 1) < P₀  →  P(T + air) < P₀
side_rules        :  sideCheck = true        （非公開、native_decide）
```

Lean: `Theorems/SidePipe.lean`、非公開の `side_rules`。

## しくみ

`sideCheck` は、土管の模様をブロックバッファに書いて `PlayerBGCollision` を動かします。着地すると、横の判定の前に状態が地面になるので、同じフレームで入ります。空中では同じ模様に止められます。

最後の 3 つの定理は [1-1 の道筋](../docs/route-1-1-ja.md) の区間 3 の計算です。`d` と `w` は [ジャンプの高さ](Jump-ja.md) から、`goal` はかたまりの右端を越えた位置です。

## 前提（Lean では証明していない）

* ルーチンは単独で確かめていて、フレームの残りとつないではいません。本物のフレームが `rule` に従うことは、[最高速の上限](TopSpeed-ja.md) と同じ種類の前提です。
* ブロックバッファは、当たり判定のコードの模様と面のデータの列から、ページ 0 に手で書いています。
* 確かめた範囲: 小さいマリオ。位置は口の 4 ピクセル左から、右側が口に入る最後の `x` まで。高さは、横が口の上の部分に届くところから、着地の深さの下まで。それより右では左側も口に届き、そこでも入れますが、
  下界にはその部分は要りません。上昇は地面より上だけ確かめました。
* `entry_after_jump`、`entry_after_step`、`slow_short` の位置とフレームは入力です。出どころは道筋のページです。

**ファイル.** `Theorems/SidePipe.lean`、非公開の `Proof/SidePipe.lean`。

**再現.**
```
.lake/build/bin/smbrta side-check     # ルーチンと規則の比較をプログラムで
```
