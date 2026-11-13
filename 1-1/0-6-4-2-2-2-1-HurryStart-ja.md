[← Back](README-ja.md) | [English](0-6-4-2-2-2-1-HurryStart.md) | [Japanese](0-6-4-2-2-2-1-HurryStart-ja.md)

# 切り替えの最後のフレームを、急ぎの音楽の歩きが要る形で

**主張.** どちらのエリアの切り替えでも、本物の走りでは、切り替えの最後のフレーム（最初に操作できるフレームのすぐ前のフレーム）は [急ぎの音楽を始めるフレームの歩き](0-6-4-2-1-HurryFrame-ja.md) が要る形で始まります（`HurryFrame.Start`）。何もしないループにいて、登場のルーチン、ゲームのモード、ゲームコアのタスクで、`DigitModifier` の 6 バイトは 0 です。条件は [1-1 全体](0-1-Route-ja.md) の切り替えの条件そのもので、`Route.Run` が求める形（`Route.ChangesK`）です。

ですから [急ぎの音楽が鳴る走り](0-6-4-HurryMusic-ja.md) で、`b` が切り替えの最後のフレームのとき、フレーム `b` の始まりはもう仮定ではありません。切り替えの段から出ます。

## なぜ最後のフレームか

切り替えの最後のフレームでは、登場のルーチンが終わり、同じフレームで操作のルーチンが動きます。そのあとタイマーのルーチンが動きます。エリアの準備がタイマーのサブカウンタを 0 にしているので、このフレームでタイマーが進みます。タイマーが 100 なら、このフレームで音楽が始まります。なので音楽の前のフレームは、最初の操作中のフレームではなく、このフレームから始まります。

## 定理

`seq` は切り替えの機械（1 つ目の切り替えは `PipeChangeEnd.PipeRunK`、2 つ目は `SidePause.EndRunQ`）、`a` は入るとき、`b` は最初の操作です。`left(m)` は切り替えの残りのフレーム数です（道筋の `left₁`、`left₂`）。

どちらの切り替えの段も `route_1_1` が使う段と同じで、音のバイトを表で持ちます。1 つ目の切り替えの段は `PipeChangeEnd.rowsKc` です（[音のバイトを表で持つ段](b-3-7-1-SoundRows-ja.md)）。縦の土管の出口での条件は `QuietP`（ポーズの音が鳴っておらず曲が表の行にある、またはポーズを解く音が鳴っている）と、ゲームのタイマーが 000 でないこと（`TimerOK`）です。2 つ目の切り替えの段は [`SideChangeSound`](d-3-4-2-SideChangeSound-ja.md) の段です。横の土管の出口での条件は `QuietK` です（ポーズの音が鳴っていない、ポーズを解く音が鳴っている、または出口のフレームでポーズを解いた）。

```
rowE(S)        :=  endOK(S)  ∧  S で DigitModifier が 0 とわかる  ∧  ルーチン = 登場、モード = ゲーム、タスク = コア（S でわかる）
rowsE(rows)    :=  ∀ 段,  statesOK(段)  ∧  (v(段) = 1  ⟹  ∀ S ∈ 段,  rowE(S))
rowsCheck₁     :  rowsE(rowsKc)  ∧  出口の参照はゲームコアでない  ∧  同じプログラム                      （hurry_rows₁、native_decide）
rowsCheck₂     :  rowsE(SideChangeSound の段)  ∧  同じプログラム                                          （hurry_rows₂、native_decide）

start_of_left       :  rowsE(l),  InvL(l, m),  left(m) = 1   ⟹   HurryFrame.Start(m)
PipeRunK.last       :  EndStatement,  PipeRunK,  exitOff,  (∀ n,  a ≤ n < b  ⟹  ¬ ctl(seq n))   ⟹   a + 1 ≤ b  ∧  InvL(rowsKc, seq (b − 1))  ∧  left(seq (b − 1)) = 1
PipeRunK.startLast  :  EndStatement,  PipeRunK,  (∀ n,  a ≤ n < b  ⟹  ¬ ctl(seq n)),  rowsCheck₁   ⟹   a + 1 ≤ b  ∧  HurryFrame.Start(seq (b − 1))
EndRunQ.startLast   :  Statement,  EndStatementK,  PipeQ,  EndRunQ,  (∀ n,  a ≤ n < b  ⟹  ¬ ctl(seq n)),  rowsCheck₂   ⟹   a + 1 ≤ b  ∧  HurryFrame.Start(seq (b − 1))
chg₁_of_changes     :  Route.ChangesK   ⟹   Chg₁
Chg₁.startLast      :  チェック,  Begin,  Chg₁            ⟹   a₁ + 1 ≤ b₁  ∧  HurryFrame.Start(base.seq (b₁ − 1))
changes_startLast   :  チェック,  Begin,  Route.ChangesK  ⟹   a₂ + 1 ≤ b₂  ∧  HurryFrame.Start(base.seq (b₂ − 1))
```

`v(段)` は段の状態の `left` の値です。`InvL(l, m)` は、`l` のある段のある状態が `m` を覆うことです。`ctl(m)` は `m` が操作できることです。

`PipeRunK.startLast` の証明です（はじめの 3 つは `PipeRunK.last`、最後の 1 つは `start_of_left` です）。

* `a` から `b` までの各機械は土管の中か、表を持つ段の中です（`PipeChangeEnd.PipeRunK.way`）。`b` より前では `left ≠ 0` です（`PipeChangeEnd.PipeRunK.first`）。どちらも `b` が入ったあとの最初の操作だから成り立ちます。
* 機械 `seq (b − 1)` は土管の中ではありません。土管の中からの 1 フレームは、土管の中で終わるか（そこでは `left ≠ 0` ですが、`seq b` は操作できるので `left(seq b) = 0` です）、出口で終わります。出口のバイトは「ゲームコアでない」と言うので（`exitOff`）、操作できません。
* なので `seq (b − 1)` は段の中です。段の 1 フレームは `left` を 1 より多く減らしません。`left(seq (b − 1)) ≤ left(seq b) + 1 = 1` です。`left ≠ 0` なので `left(seq (b − 1)) = 1` です。
* `seq (b − 1)` を覆う状態は `v = 1` の段にあります（`left_of_covered`）。`rowsE` から、その状態は `rowE` のとおりです。なので `seq (b − 1)` は何もしないループにいて、登場のガードのバイトと `DigitModifier` 0 を持ちます（`start_of_rowE`、`known_E`）。

2 つ目の切り替えでは、はじめの 3 つの段階が `SidePause.EndRunQ.last` です。機械 `seq (b − 1)` は `SideChangeSound` の段の中にあり、`left` は 1 です。`EndRunQ.startLast` はこの段に `start_of_left` を使います。

`Route.Base` のフレームでは、`Chg₁.startLast` が `Chg₁` から 1 つ目の切り替えの `PipeRunK` を作ります（`Chg₁.run₁`。`Route.ChangesK.run₁` と同じ）。入るときの条件はタイトルで Start を押したことから出ます（`Chg₁.entry`。`Route.Run.entry₁` と同じ）。`b₁` は選び方から入ったあとの最初の操作です（`Chg₁.ctlFirst`）。`changes_startLast` は `Route.Run.atCtl₀` と同じく `Route.ChangesK.run₂` を使います。`b₂` は選び方から入ったあとの最初の操作です（`ChangesBase.ctlFirst₂`）。

`Chg₁` は `Route.ChangesK` の 1 つ目の切り替えのフィールドです。`entryRest₁`、`upClean₁`、`ctlBy₁`、`paused₁`、`places₁`、`noStart₁`、`quiet₁`、`time₁` です。どれも `Route.ChangesK` の同じ名前のフィールドと同じ命題なので、`Route.ChangesK` から `Chg₁` が出ます（`chg₁_of_changes`）。別の構造にしたのは、部屋で音楽が始まる走りは 2 つ目の切り替えの `entry₂`（横の土管の入口での音楽のバイト）を満たさないからです。

## チェック

段の状態です（1 つ目の切り替えの段 `rowsKc`、2 つ目の `SideChangeSound` の段。`hurry-rows-check FM2`）。

| 段 | 段の数 | `left` が 1 の状態 | そのうち `rowE` のとおりのもの |
|---|---|---|---|
| 1 つ目の切り替え、`rowsKc` | 44 | 2 | 2 |
| 2 つ目の切り替え、`SideChangeSound` の段 | 123 | 2 | 2 |

操作できる状態（`left` 0）も `DigitModifier` 0 と `endOK` がわかります（どちらの切り替えでも 4）。登場のルーチンにある段の状態も全部そうです。1 つ目の切り替えで 34、2 つ目で 192 です。切り替えはエリアを準備するときにこれらのバイトを 0 にします。表を持つ段は音のバイトを忘れていますが、`rowE` は音のバイトを読みません。

チェックはプログラムで 26 秒（`rowsCheck₁`）と 19 秒（`rowsCheck₂`）です。どちらも切り替えの段をもう一度作ります。26 秒のうち 24 秒が `rowsKc`、19 秒のうち 15 秒が `SideChangeSound` の段です。`route_1_1` も自分のチェック（`pipe_end`、`side_sound_checks`）で段を作ります。前の `rowsCheck₁` は段 `rowsA`、`rowsB` を読みました（2.7 秒）。その出口の条件はもっと強いものでした。非公開の `Proof/HurryMusic.lean` は、この 2 つのチェックと `hurry_near_check` 込みで 55 秒でビルドできます（前は 27 秒から 36 秒）。

## 本物のフレームで

* 動画: 動画のフレーム 652 と 1045（電源を入れてから）は、どちらも登場のルーチンで始まり、操作できる状態で終わります。どちらも `HurryFrame.Start` のとおりに始まり、`DigitModifier` は 0 です（`hurry-rows-check`）。
* `hurry-check FM2`: 音楽を始める最初のフレーム 108 のうち 58 は切り替えのあとです。そこでのフレーム `b` は、操作できない状態で終わる最後のフレームの次のフレーム、つまり切り替えの最後のフレームです。58 全部で `HurryFrame.Start` のとおりに始まります。

## 仮定（Lean で証明していないこと）

これ自身の仮定はありません。`Route.Run` と同じく切り替えの条件を使います。1 つ目の切り替えには `Chg₁`（`Route.ChangesK` の 1 つ目の切り替えのフィールド）、両方には `Route.ChangesK` です。[道筋のページ](0-1-Route-ja.md) に並べてあります。

仮定でなくなったもの: `HurryMusic.Run` のフィールド `start` のうち、`b` が切り替えの最後のフレームのときのフレーム `b` の状態。新しいもの: ROM のチェック `rowsCheck₁` と `rowsCheck₂`、`start` の中の切り替えの条件。この条件は、`Route.Run` が求める `Route.ChangesK` の条件そのものになりました。横の土管の出口で `Quiet` のかわりに `QuietK` です。なので横の土管のフレームで Start を押す走りも含まれます。縦の土管の出口で `Quiet ∧ SongAt(song) ∧ SongAt(xshape)` のかわりに `QuietP ∧ SongAt(xshape)`、`TimeOK`（タイマーが 000 でなく、音のポーズのフラグが 0）のかわりに `TimerOK`（ゲームのタイマーが 000 でない）です。なので出口でポーズを解く音が鳴っている走りも含まれます。

**ファイル.** `Theorems/HurryStart.lean`（`PipeRunK.last`、`PipeRunK.startLast`、`Chg₁`、`chg₁_of_changes`）、`Theorems/HurryMusic.lean`（`Run.startB`）、非公開の `Proof/HurryMusic.lean`（`hurry_rows₁`、`hurry_rows₂`）。

**再現.**
```
.lake/build/bin/smbrta hurry-rows-check FM2      # 両方の切り替えの段、チェック、動画の切り替えの最後のフレーム（約 110 秒）
```
