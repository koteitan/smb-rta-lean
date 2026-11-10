[← Back](README-ja.md) | [English](a-5-9-MoveEnd.md) | [Japanese](a-5-9-MoveEnd-ja.md)

# 移動の終わりの位置

**主張.** [1 フレーム全部](a-5-2-PipeWrites-ja.md) の抽象機械は、位置を右足の入口ではなく、移動の終わり（`PlayerSubs`）で分けるようになりました。そこからスクロールのルーチン、画面の外のビット、当たりの箱、頭の判定、左足を通って右足まで、位置を追います。だから入るフレームでは、書き込みより前の移動の終わりの位置は、土管の範囲の左端より左ではありません。これはフレームのモデルの `P₂` です。

前の仮定 `pos`（「`P₂` は右足の入口の位置」）はなくなりました。かわりの仮定は 2 つです。

* `moved`: `P₂` は移動の終わりの位置です。フレームのモデルは `P₂` をこう作ります（`FrameModel.frame_read`）。
* `edge`: 書き込みまでに、フレームは 2 つの場所に来ません。スクロールのルーチンが位置を書く命令と、頭がブロックに当たったときのルーチンです。

名前は [1 フレーム全部](a-5-2-PipeWrites-ja.md) と同じです。`tr_t(j)` はフレーム `t` の `j` 命令あとの機械です。`posP(m) = 256·(256·page(m) + x(m)) + 小数部(m)`、`L = 256·L_px` は範囲の左端です。

```
w_edge          :=  スクロールのルーチンが Player_X_Position を書く STA  （その部分 KeepOnscr は画面の端に彼を戻す）
h               :=  頭がブロックに当たったときのルーチン  （PlayerHeadCollision）
G_S             :=  guardOf  で  subs := PlayerSubs,  cuts := [w_edge, h]

HypG(m)         :=  (subs = 0  →  AtEntry(m) → px(m) < L_px)  ∧  (AtRead(m) → TilesOK(m))
                    ∧  (subs ≠ 0  →  pc(m) = subs → px(m) < L_px)  ∧  pc(m) ∉ cuts
```

2 つの場所は ROM から探します。`w_edge` は、`PlayerSubs` が最初に呼ぶルーチンの中の、`Player_X_Position` への最初の `STA` です。`h` は、当たり判定のルーチンの `JMP DoFootCheck` の直前に呼ぶルーチンです。記号は足していません。

```
entry_right_of_leftS :  ruleCheckS,  Enters(m, i),  FrameStart(m),
                        (∀ n,  WriteStep(n) → ∀ j ≤ n,  Clean(tr(j)) ∧ (AtRead(tr(j)) → TilesOK(tr(j))) ∧ pc(tr(j)) ≠ w_edge ∧ pc(tr(j)) ≠ h)
                        →  ∃ n j,  WriteStep(n) ∧ j ≤ n ∧ pc(tr(j)) = PlayerSubs ∧ L_px ≤ px(tr(j))
rule_on_framesS      :  ruleCheckS,  start, clean, tiles は rule_on_frames のとおり,
                        edge:   ∀ t,  Enters(fm t, inp t) → ∀ n, WriteStep(n) → ∀ j ≤ n,  pc(tr_t(j)) ≠ w_edge ∧ pc(tr_t(j)) ≠ h
                        moved:  ∀ t,  Enters(fm t, inp t) → ∀ n j,  WriteStep(n) → j ≤ n → pc(tr_t(j)) = PlayerSubs → P₂(t) = posP(tr_t(j))
                        →  ∀ t,  Enters(fm t, inp t)  →  L ≤ P₂(t)
pipe_frame_check（非公開）   :  ruleCheckS(sy, m₀) = true（native_decide）
pipe_no_entry_real（非公開） :  Enters(fm E, inp E),  FrameStart(fm E),  clean, tiles, edge, moved,  openP, openB,  機械から読むフレーム  →  367 < E
```

`ruleCheckS` は `PlayerSubs ≠ 0` と、`G_S` での抽象機械の確認です。前の `entry_right_of_left` と `rule_on_frames`（右足で分ける）も残しています。`Route` はもう使いません。

ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/PipeWrites.lean`（`Guard` の欄 `subs`、`cuts`。`splitPos`、`cov_split`、`guardS`、`ruleCheckS`、`entry_right_of_leftS`、`rule_on_framesS`）、`Theorems/Route.lean`（`Pipe.edge`、`Pipe.moved`）、非公開の `Proof/PipeWrites.lean`。

## しくみ

* **分け方.** `PlayerSubs` で、`px < L_px` の仮定のもとに、位置の値ごとに 1 つの片を作ります。916 個です。証明は右足で分けるときと同じです（`cov_split`）。
* **切る場所.** `w_edge` と `h` では片を作りません。フレームがそこに来ないことは `HypG` が言います。
* **探索（証明の一部ではない）.** `PlayerSubs` から当たり判定のルーチンが戻るまで、探索は位置を覚えていて、位置で状態を分けておきます。戻るところ、足の判定の出口、右足の読みで位置を忘れます。
* **頭の当たりを切る理由.** このルーチンは、抽象機械が行き先を知らない添字で書きます（`X = SprDataOffset_Ctrl` での `Block_State,X`、画面のバッファ）。そういう書き込みのあと、抽象機械は `Prot` の外のバイトを全部忘れます。位置も忘れます。位置を `Prot` に入れることはできません。移動そのものが位置を添字で書くので（`STA SprObject_X_Position,X`）、`Clean` が操作できるフレームで成り立たなくなります。またこのルーチンは縦の速さを 0 にすることがある（壊れないブロック）ので、同じフレームでの着地を抽象機械は除けません。
* **`h` を切らないと**: 失敗が 223,149 回あります。位置がわからないまま書き込みに来る道です。2 つとも切ると 0 回です。

**大きさ.** 3,209,542 歩、分かれ 300,327、失敗 0、表 150,681。プログラムで、探索が約 8〜11 秒、確認が約 22〜30 秒です。前の抽象機械は 1,504,949 歩、確認が約 6 秒でした。

## 本物のフレームで確かめたこと

プログラム（`pipe-subs-check`）です。走りは [1 フレーム全部](a-5-2-PipeWrites-ja.md) の `pipe-rule-check` と同じです。

| 走り | フレーム | 操作できる状態で始まる | 入るフレーム | 切る場所に来る操作中のフレーム |
|---|---|---|---|---|
| TAS の入るまで | 368 | 368 | 1 | 1 |
| TAS の入ったあと | 1,300 | 351 | 0 | 1 |
| 入る前の状態から: 歩いて下 | 5,480 | 5,480 | 161 | 0 |
| 入る前の状態から: 跳んで下を押して着地 | 25,308 | 24,161 | 14 | 0 |
| 入る前の状態から: ランダムな入力 | 26,855 | 26,295 | 1 | 7 |
| 同じ、大きいマリオに書きかえ | 9,000 | 8,570 | 0 | 21 |

入る 177 フレームすべてで:
* 書き込みより前の命令は `w_edge` にも `h` にもない（`edge`）。
* 書き込みより前に `PlayerSubs` に 1 回だけ来る。
* そこで `posP = posP（フレームの始まり） + 16·v`。`v` はそこの速さ。フレームのモデルの移動（`P₂ = P + 16·v₂`）です。
* そこで `px ≥ L_px`。その `px` は右足の入口の位置と同じ。

`FrameStart`、`Clean`、`TilesOK` は、前と同じくどのフレームでも成り立ちます。

## 変わったこと

* **もう仮定しないこと:** 移動の終わりから足の判定までに、何も彼を動かさないこと。抽象機械が証明します。スクロールのルーチン（端で書く命令を除く）、画面の外のビット、画面の上の位置、当たりの箱、頭の判定、左足です。
* **新しい仮定:** `edge`。入るフレームの、書き込みまでの命令についての条件です。
* **`moved`** は `P₂` が何かを言います。本物のフレームから `Frame` を作るときに、フレームのモデルが使う定義です。

## 仮定（Lean で証明していない）

* **`moved`.** 本物のフレームから `Frame` を作る話（項目 0-0-0-3-1）の一部です。
* **`edge`.** 入るフレームは、書き込みまでに、画面の端にいないし、頭でブロックに当たらない。
* [1 フレーム全部](a-5-2-PipeWrites-ja.md) のほかの仮定: `FrameStart`、`Clean`、`TilesOK`。

**ファイル.** `Theorems/PipeWrites.lean`、`Theorems/Route.lean`、非公開の `Proof/PipeWrites.lean`。

**再現.**
```
.lake/build/bin/smbrta pipe-subs-search       # 移動の終わりで分ける抽象機械: 探索と確認、約 1 分
.lake/build/bin/smbrta pipe-subs-check FM2    # 確認と、本物のフレームでの条件、約 3 分
```
