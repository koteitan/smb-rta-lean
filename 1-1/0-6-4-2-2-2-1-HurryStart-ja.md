[← Back](README-ja.md) | [English](0-6-4-2-2-2-1-HurryStart.md) | [Japanese](0-6-4-2-2-2-1-HurryStart-ja.md)

# 切り替えの最後のフレームを、急ぎの音楽の歩きが要る形で

**主張.** どちらのエリアの切り替えでも、本物の走りでは、切り替えの最後のフレーム（最初に操作できるフレームのすぐ前のフレーム）は [急ぎの音楽を始めるフレームの歩き](0-6-4-2-1-HurryFrame-ja.md) が要る形で始まります（`HurryFrame.Start`）。何もしないループにいて、登場のルーチン、ゲームのモード、ゲームコアのタスクで、`DigitModifier` の 6 バイトは 0 です。条件は [1-1 全体](0-1-Route-ja.md) の切り替えの条件です。

ですから [急ぎの音楽が鳴る走り](0-6-4-HurryMusic-ja.md) で、`b` が切り替えの最後のフレームのとき、フレーム `b` の始まりはもう仮定ではありません。切り替えの段から出ます。

## なぜ最後のフレームか

切り替えの最後のフレームでは、登場のルーチンが終わり、同じフレームで操作のルーチンが動きます。そのあとタイマーのルーチンが動きます。エリアの準備がタイマーのサブカウンタを 0 にしているので、このフレームでタイマーが進みます。タイマーが 100 なら、このフレームで音楽が始まります。なので音楽の前のフレームは、最初の操作中のフレームではなく、このフレームから始まります。

## 定理

`seq` は切り替えの機械（`PipeChangeEnd.PipeRun` または `SideChangeEnd.EndRun`）、`a` は入るとき、`b` は最初の操作です。`left(m)` は切り替えの残りのフレーム数です（道筋の `left₁`、`left₂`）。

```
rowE(S)        :=  endOK(S)  ∧  S で DigitModifier が 0 とわかる  ∧  ルーチン = 登場、モード = ゲーム、タスク = コア（S でわかる）
rowsE(rows)    :=  ∀ 段,  statesOK(段)  ∧  (v(段) = 1  ⟹  ∀ S ∈ 段,  rowE(S))
rowsCheck₁     :  rowsE(rowsA)  ∧  rowsE(rowsB)  ∧  出口の参照はゲームコアでない  ∧  同じプログラム      （hurry_rows₁、native_decide）
rowsCheck₂     :  rowsE(rows0)  ∧  rowsE(rows1)  ∧  同じもの                                             （hurry_rows₂、native_decide）

start_of_left       :  rowsE(l),  InvL(l, m),  left(m) = 1   ⟹   HurryFrame.Start(m)
PipeRun.startLast   :  EndStatement,  PipeRun,  (∀ n,  a ≤ n < b  ⟹  left(seq n) ≠ 0),  rowsCheck₁   ⟹   a + 1 ≤ b  ∧  HurryFrame.Start(seq (b − 1))
EndRun.startLast    :  Statement,  EndStatement,  EndRun,  （left について同じ）,  rowsCheck₂       ⟹   a + 1 ≤ b  ∧  HurryFrame.Start(seq (b − 1))
Chg₁.startLast      :  チェック,  Begin,  Chg₁          ⟹   a₁ + 1 ≤ b₁  ∧  HurryFrame.Start(base.seq (b₁ − 1))
changes_startLast   :  チェック,  Begin,  Route.Changes ⟹   a₂ + 1 ≤ b₂  ∧  HurryFrame.Start(base.seq (b₂ − 1))
```

`v(段)` は段の状態の `left` の値です。`InvL(l, m)` は、`l` のある段のある状態が `m` を覆うことです。

`PipeRun.startLast` の証明です。

* `a` から `b` までの各機械は土管の中か段の中です（`PipeRun.way`。`PipeChangeEnd.PipeRun.bound` と同じ帰納法）。`b` より前で `left ≠ 0` なので、`left` が 0 の場合は除かれます。
* 機械 `seq (b − 1)` は土管の中ではありません。土管の中からの 1 フレームは、土管の中で終わるか（そこでは `left ≠ 0` ですが、`seq b` は操作できるので `left(seq b) = 0` です）、出口で終わります。出口のバイトは「ゲームコアでない」と言うので（`exitOff`）、操作できません。
* なので `seq (b − 1)` は段の中です。段の 1 フレームは `left` を 1 より多く減らしません。`left(seq (b − 1)) ≤ left(seq b) + 1 = 1` です。`left ≠ 0` なので `left(seq (b − 1)) = 1` です。
* `seq (b − 1)` を覆う状態は `v = 1` の段にあります（`left_of_covered`）。`rowsE` から、その状態は `rowE` のとおりです。なので `seq (b − 1)` は何もしないループにいて、登場のガードのバイトと `DigitModifier` 0 を持ちます（`start_of_rowE`、`known_E`）。

`EndRun.startLast` は 2 つ目の切り替えで同じことをします（`EndRun.way` は `ControlStart.EndRun.inRows` の帰納法です）。

`Route.Base` のフレームでは、`Chg₁.startLast` が `Chg₁` から 1 つ目の切り替えの `PipeRun` を作ります（`Chg₁.run₁`。`Route.Changes.run₁` と同じ）。入るときの条件はタイトルで Start を押したことから（`Chg₁.entry`。`Route.Run.entry₁` と同じ）、`left ≠ 0` は出口での時間から出ます（`PipeChangeEnd.PipeRun.first`）。`changes_startLast` は `Route.Run.atCtl₀` と同じく `Route.Changes.run₂` と `SideChangeEnd.EndRun.firstF` を使います。

`Chg₁` は `Route.Changes` の 1 つ目の切り替えの条件です。`entryRest₁`、`upClean₁`、`ctlBy₁`、`paused₁`、`places₁`、`quiet₁`、`noStart₁`、`time₁` です。別の構造にしたのは、部屋で音楽が始まる走りは 2 つ目の切り替えの `entry₂`（横の土管の入口での音楽のバイト）を満たさないからです。

## チェック

段の状態です（1 つ目の切り替えの段 `rowsA`、`rowsB`、2 つ目の `rows0`、`rows1`。`hurry-rows-check FM2`）。

| 段 | 段の数 | `left` が 1 の状態 | そのうち `rowE` のとおりのもの |
|---|---|---|---|
| 1 つ目の切り替え、`rowsA` と `rowsB` | それぞれ 44 | それぞれ 2 | 全部 |
| 2 つ目の切り替え、ポーズのフラグ 0 | 123 | 2 | 2 |
| 2 つ目の切り替え、ポーズのフラグ 0 でない | 123 | 2 | 2 |

操作できる状態（`left` 0）も `DigitModifier` 0 と `endOK` がわかります（どの場合も 2）。登場のルーチンにある段の状態も全部そうです。1 つ目の切り替えの時間の段で 34、2 つ目のそれぞれの場合で 192 です。切り替えはエリアを準備するときにこれらのバイトを 0 にします。

チェックはプログラムで 2.8 秒（`rowsCheck₁`）と 1.6 秒（`rowsCheck₂`）です。非公開の `Proof/HurryMusic.lean` は、この 2 つのチェックと `hurry_near_check` 込みで 8.1 秒でビルドできます。

## 本物のフレームで

* 動画: 動画のフレーム 652 と 1045（電源を入れてから）は、どちらも登場のルーチンで始まり、操作できる状態で終わります。どちらも `HurryFrame.Start` のとおりに始まり、`DigitModifier` は 0 です（`hurry-rows-check`）。
* `hurry-check FM2`: 音楽を始める最初のフレーム 108 のうち 58 は切り替えのあとです。そこでのフレーム `b` は、操作できない状態で終わる最後のフレームの次のフレーム、つまり切り替えの最後のフレームです。58 全部で `HurryFrame.Start` のとおりに始まります。

## 仮定（Lean で証明していないこと）

これ自身の仮定はありません。`Route.Run` と同じく切り替えの条件を使います。1 つ目の切り替えには `Chg₁`、両方には `Route.Changes` です。[道筋のページ](0-1-Route-ja.md) に並べてあります。

仮定でなくなったもの: `HurryMusic.Run` のフィールド `start` のうち、`b` が切り替えの最後のフレームのときのフレーム `b` の状態。新しいもの: ROM のチェック `rowsCheck₁` と `rowsCheck₂`、`start` の中の切り替えの条件。

**ファイル.** `Theorems/HurryStart.lean`、`Theorems/HurryMusic.lean`（`Run.startB`）、非公開の `Proof/HurryMusic.lean`（`hurry_rows₁`、`hurry_rows₂`）。

**再現.**
```
.lake/build/bin/smbrta hurry-rows-check FM2      # 両方の切り替えの段、チェック、動画の切り替えの最後のフレーム（約 30 秒）
```
