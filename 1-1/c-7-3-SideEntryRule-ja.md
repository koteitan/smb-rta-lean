[← Back](README-ja.md) | [English](c-7-3-SideEntryRule.md) | [Japanese](c-7-3-SideEntryRule-ja.md)

# 横の土管に入るフレームを本物のフレームで

**主張.** これは部分的な結果です。「横の土管に入る」を本物の機械の上で定義します。あるフレームが入るなら、そのフレームの横の判定がページを読むとき、マリオの位置は土管の口の左端より左ではありません。ですから `RoomJoin` の仮定 `entry`、`entry_mem`、`entered`、`entry_P` はなくなります。この 4 つは、手で書いたブロックバッファ（`SidePipe.withPipe`）の上で判定のルーチンだけを動かして入る、という仮定でした。証明は横の判定の 1 回の通過を抽象機械で追います。フレームの残りは追いません。残りは仮定 `Pass` と `pos` です。

**今.** `RoomRun` はもうこのページの定理を使いません。[横の土管に入るフレーム: 1 フレーム全部](c-7-16-SideFrame-ja.md) がフレーム全部を追い、`Pass` と `pos` はもう欄ではありません。ここの定理は残します。読んだバイトの片（`pieces`）はそこで使います。

やり方は [旗に触るフレームを本物のフレームで](f-6-1-PoleEntryRule-ja.md) と同じです。横の判定は同じで、書き込みの命令、タイル、出口、ページが違います。

`frame(m, i)` は入力 `i` の本物の 1 フレームです。`tr(n)` は、そのフレームの `n` 命令あとの機械です。`rt(m)` は `GameEngineSubroutine` です。`e_s` は横の土管のルーチンの番号です。`page(m)` は `Player_PageLoc`、`x(m)` は `Player_X_Position` です。`w` は `ChkGERtn` の中で `rt` を書く命令です。`T₁` は横の土管のタイル、`T₂` は `ContSChk` のあとの最初の比較の値です。判定のルーチンは、この 2 つのどちらかで入ります。`col` は土管の列、`d_C` はブロックバッファの中のその列の一番上の場所です。`R` はブロックバッファの行の数です。`x₀` は右側が口に入る最初の `x`、`P₀ = 256·x₀` は口の左端の位置です（[横の土管に入る](c-4-SidePipe-ja.md)）。

```
WriteStep(n)    :=  rt(tr(n)) ≠ e_s  ∧  rt(tr(n + 1)) = e_s
Enters(m, i)    :=  ∃ n,  WriteStep(n)
EndsEntry(m, i) :=  rt(m) ≠ e_s  ∧  rt(frame(m, i)) = e_s
px(m)           :=  256·page(m) + x(m)

Start(m)        :=  pc(m) = DoPlayerSideCheck、スタックポインタは決まった値、足し算の番号のバイトは大きいマリオか小さいマリオの値、
                    ドットは vblank が終わったあとでフレームの終わりより前、NMI も vblank もなし、ストローブなし
AtEntry(m)      :=  pc(m) = BlockBufferCollision の中でページを読む命令  ∧  レジスタ Y は横の判定の番号  ∧  レジスタ X = 0
AtRead(m)       :=  pc(m) = このルーチンの `LDA (zp),Y`
RowOK(m)        :=  Y mod 16 = 0  ∧  Y < 16·R
TilesOK(m)      :=  ∀ ブロックバッファの場所 d,  mem(d) ∈ {T₁, T₂}  →  ∃ r < R,  d = d_C + 16·r
Pass(n)         :=  pc(tr(n)) = w  ∧  ∃ n₀ ≤ n,  Start(tr(n₀))
                    ∧  (∀ j ∈ [n₀, n],  pc(tr(j)) ∉ 出口)
                    ∧  (∀ j ∈ [n₀, n),  AtRead(tr(j))  →  RowOK(tr(j)) ∧ TilesOK(tr(j)))
出口            :=  ExSCH、ExCSM、`ContSChk` の前の命令（登るルーチンへのジャンプ）、ErACM（コイン）、ImpedePlayerMove（止める）
pos(P)          :=  ∀ n j,  WriteStep(n)  →  j < n  →  AtEntry(tr(j))  →  ∃ f ≥ 0,  P = 256·px(tr(j)) + f
```

`TilesOK` は旗のものと同じ式です。旗のページの条件は、ページが 0 なので、いつも成り立ちます。

```
no_write             :  walkCheck,  s(j + 1) = step(s(j)) (j < n),  Start(s(0)),
                        (∀ j < n,  AtEntry(s(j)) → px(s(j)) < x₀),  (∀ j < n,  AtRead(s(j)) → RowOK ∧ TilesOK),
                        出口に行かない (j ≤ n)                                  →  pc(s(n)) ≠ w
entry_right_of_left  :  ruleCheck,  Enters(m, i),  (∀ n,  WriteStep(n) → Pass(n))
                        →  ∃ n j,  WriteStep(n) ∧ j < n ∧ AtEntry(tr(j)) ∧ x₀ ≤ px(tr(j))
mouth_of_pass        :  ruleCheck,  Enters(m, i),  (∀ n,  WriteStep(n) → Pass(n)),  pos(P)  →  P₀ ≤ P
enters_of_ends       :  EndsEntry(m, i)  →  Enters(m, i)
PassR(n)             :=  読みで RowOK だけを求める Pass(n)（TilesOK なし）
pass_of              :  PassR(n),  (∀ j < n,  AtRead(tr(j)) → TilesOK(tr(j)))  →  Pass(n)
RoomRun.mouth_of     :  Checks,  RoomRun  →  P₀ ≤ P(E)
side_rule_check（非公開） :  ruleCheck(sy, m₀) = true（native_decide）
```

ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/SideEntryRule.lean`、`Theorems/RoomJoin.lean` の `RoomRun`、非公開の `Proof/SideEntryRule.lean`（`side_rule_check`）。

`RoomJoin` のフィールドは次のように変わりました。

* なくなったもの: `entry`、`entry_mem`、`entered`、`entry_P`（`RoomFields`）。`Checks.side` は `Checks.sideRule` になりました。
* 増えたもの: `enters`（`Enters(fm(E − 1), pad(E))`、フレーム `E` の始めの機械と入力）、`pass`（`∀ n, WriteStep(n) → Pass(n)`）、`pos`（`pos(P(E))`）。どれも `RoomRun` のフィールドで、フレーム `E` だけについての事実です。`RoomCore.mouth`（`P₀ ≤ P(E)`）は、これらから `RoomRun.mouth_of` が作ります。今は `pass` は `PassR(n)` を与え、タイルは別のフィールド `tiles`（`∀ n j, WriteStep(n) → j < n → AtRead(tr(j)) → TilesOK(tr(j))`）です。`pass_of` が 2 つを合わせます。

前の `entry_ground`（入る状態は地面にある）はなくなりました。証明では使っていませんでした。

## しくみ

**抽象機械.** [旗に触るフレームを本物のフレームで](f-6-1-PoleEntryRule-ja.md) と同じ機械、同じ始めの状態です。わかっているのはスタックポインタと足し算の番号だけです。

**3 つの場所で分けます.** 位置の足し算の前とページを読む前は旗と同じです。ページを読む前は、仮定 `px < x₀` のもとで分けます。口は 0 ページにあるので、ページは 0 だけで、`x < x₀` です。これでポインタの値がわかり、右側の読みも土管の列より左です。

**読むバイトの分け方.** ここが旗と違います。旗の 2 つのタイルは 1 ビットだけ違います。`T₁` と `T₂` は 5 ビット違います。なので「`T₁` のあるビットと違う」という 1 ビットの部分では、`T₂` を除けません。部分は次の 8 個です。

* 2 つのタイルが同じ値のビット（3 個）で、その値と違う。
* 2 つのタイルが違う値のビットを順に `d₀ … d₄` とします。`k` ごとに、`d_k` が `T₂` の値で、`d_{k+1}`（`d₅ = d₀`）が `T₁` の値。5 個です。

どちらのタイルでもないバイトは、どれかの部分に入ります。違うビットだけを見ると、`T₁` と `T₂` はちょうど反対です。どちらでもないバイトは、同じ値のビットで両方と違うか、違うビットの上で「`T₂` の値の次が `T₁` の値」の場所を輪の中に持つからです。`piecesCover` が 256 個の全部のバイトで確かめます。どの部分も、2 つのタイルのどちらとも違うことがわかっています。

**読んだ値のその後.** 読んだバイトは `A` に残り、`ChkPBtm` の 2 つの `CMP` に来ます。わかっているビットから、どちらとも等しくないとわかり、止めるルーチン（出口）に行きます。ですから `w` に行く道はありません。

**大きさ.** 38,814 ステップ、21,028 の枝分かれ、失敗 0、表 1,412。プログラムで約 2 秒、非公開の証明のビルドで約 3 秒です。

## `rt` に横の土管の番号を書く命令

コードから読みました。証明ではありません。`rt` を直接書く 12 個の命令のうち、横の土管の番号を書くのは `ChkGERtn` の `w` だけです。`w` に来るのは `ChkPBtm` の比較で 2 つのタイルのどちらかに等しいときだけで、そこに来るのは横の判定の `CheckSideMTiles` からだけです。

添字つきの書き込みやポインタを通す書き込みで `rt` が `e_s` になるフレームは、`Enters` を満たします。しかし `Pass` の `pc(tr(n)) = w` を満たしません。ですから `RoomRun` の仮定がこれを除きます。本物のフレームでは出ません。

## 本物のフレームで確かめたこと

プログラムです（`side-rule-check`）。

| 走り | フレーム | 横の判定（操作） | 読み | 入ったフレーム |
|---|---|---|---|---|
| 動画の部屋（最初の操作から入るフレームのあと 3 フレームまで） | 113 | 103 | 406 | 1 |
| 部屋の動画のフレームから、右へ向かう乱数の入力（200 回） | 45,123 | 44,638 | 174,758 | 67 |
| 入る 12、8、5、3 フレーム前から、左、右、A、B の全部の入力を 5 フレーム | 11,072 | 11,072 | 43,280 | 352 |
| 口の近くの高さ、位置、状態、向きごとの 1 フレーム。書き換え | 38,400 | 22,110 | 75,944 | 1,295 |

* どの行でも、操作のフレームの横の判定はすべて `Start` を満たします。すべての読みは `RowOK` と `TilesOK` を満たします。
* 入ったフレームは全部 `w` で書き、全部 1 回の通過の終わりです。口の左端より左はありません。ページを読むときの位置は、フレームの終わりの位置から端数を除いたものです（`pos`）。入るフレームは、フレームの終わりで横の土管のルーチンになっています（`EndsEntry`）。
* 動画: 部屋の最初の操作は動画のフレーム 653 のあと、入るのはその 111 フレームあとです。そのとき土管の列と次の列のブロックバッファは、下から 3 行目が `T₁` とその次、その上が土管の上のタイルとその次です。`SidePipe.withPipe` と同じです。
* 位置は口の左端から 0 から 21 ピクセルに出ます。高さは地面の上だけです。

## 前提（Lean では証明していない）

* **`Pass` の書き込みの部分.** `rt` を `e_s` にする命令は `w` だけ。そのフレームの中で、それより前に横の判定を始めている。そこから出口に行っていない。コードから読みました。上の表の本物のフレームで確かめました。フレームの残り（NMI、音、画面、敵）は追っていません。
* **`Start`.** スタックポインタ、足し算の番号、ドット、フラグです。旗と同じです。
* **`RowOK`.** コードから読みました。旗と同じです。
* **`TilesOK`.** 2 つのタイルは、ブロックバッファの中で土管の列にしかない。[部屋のブロックの地図](c-7-12-RoomMap-ja.md) が、部屋への切り替えと部屋からの切り替えの機械（`Route.Changes`）の上で、部屋のどのフレームのどの読みでも証明します。使う仮定は、部屋のフレームがそこですでに仮定しているもの（`SiteOK`）です。`Route.Run.roomTiles` が、定理 `Route.Run.roomEnter` で `RoomRun` のフレーム `E` をその機械につなぎます。欄 `tiles` はなくなりました。
* **`pos`.** `P(E)` はページを読むときの位置です。本物のフレームから `Frame` を作る話の一部です。もう `RoomRun` の欄ではありません。[1 フレーム全部](c-7-16-SideFrame-ja.md) は、移動の終わりの `P(E)` だけを使います（`movedE`）。
* **右端、高さ、地面.** ここでは左端だけを出します。`RoomJoin` が使うのは左端だけです。

**ファイル.** `Theorems/SideEntryRule.lean`、非公開の `Proof/SideEntryRule.lean`。

**再現.**
```
.lake/build/bin/smbrta side-rule-check FM2 [N]    # 1 回の通過の確認と、本物のフレームでの仮定。N は乱数の走りの数
```
