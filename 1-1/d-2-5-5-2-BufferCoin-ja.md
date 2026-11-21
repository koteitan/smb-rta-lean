[← Back](README-ja.md) | [English](d-2-5-5-2-BufferCoin.md) | [Japanese](d-2-5-5-2-BufferCoin-ja.md)

# 制御 6 で口より左から始まるフレームは入らない

**主張.** 部屋のフレームが、画面のバッファの制御 6、ページ 0、位置 16 から 180 px で始まるなら、そのフレームは横の土管に入りません。証明しました。ROM の確認は 1 つです（部屋のフレームの歩き 7 つ、表は 1 つ、ラウンド 25 からネイティブで約 1.5 分）。それと [SideFrame](c-7-16-SideFrame-ja.md) の 1 フレーム全体の歩き（`side_frame_check`、前に証明済み）を使います。そこでフィールド `buffer₂` が求めることは減りました。入るフレームの前のフレームがコインを消したなら（そのとき制御は 6）、そのフレームはページ 0 の 16 から 180 px で終わる、ということだけです。本物の走りでは、コインのフレームは 52 から 173 px で終わります。いつもそうなることは証明していません。

名前は [部屋を通る画面のバッファの制御](d-2-5-5-1-BufferControl-ja.md) のものです。`x(m)` と `page(m)` はプレイヤーのページ上の位置とページです（`Player_X_Position`、`Player_PageLoc`）。`Q` は動きの終わり（`PlayerSubs`）、`xLo = 195 px` は口の左端です。`r₆(a)` は部屋の基準の機械で、`c = 6`、`page = 0`、`x` を区間 `a` の値にしたものです。`K_G(a) := K_B ∪ { page のすべてのビット } ∪ { a の分かっているビット }` です。

## 主張の式

```
pieces         :=  [16, 32), [32, 64), [64, 128), [128, 160), [160, 176), [176, 180), {180}       （合わせて [16, 181)）
walkA(a)       :=  (r₆(a), K_G(a)) からの歩きが通り、その表の Q のどの状態もページ 0 で、その区間のどの x も xLo より小さい
coinCheck      :=  区間が [16, 181) を覆い、K_T は x も page も c も挙げず、この 3 つは別のバイトで、∀ a ∈ pieces,  walkA(a)

subs_left      :  walkA(a),   RoomCond(r₆(a), K_G(a), m),   ∀ j, SiteOK(tr(j))
                  →   ∀ j,  frame(tr(j)) ≤ frame(m),  pc(tr(j)) = Q   →   256·page(tr(j)) + x(tr(j)) < xLo
cond_piece     :  RoomCond(r, K_T, m),   c(m) = 6,   page(m) = 0,   x(m) ∈ a            →   RoomCond(r₆(a), K_G(a), m)
no_enter       :  [b, a) で RoomMap.map_of_rows の条件,   coinCheck,   sideFrameCheck,   b ≤ k < a,
                  Enters(seq k),   c(seq k) = 6,   page(seq k) = 0,   16 ≤ x(seq k) < 181          →   False

Run.coin₂      :  c(seq(a₂ − 1)) = 6,   page(seq(a₂ − 1)) = 0,   16 ≤ x(seq(a₂ − 1)) < 181     →   False          （定理、新しい）
Run.buffer₂    :  c(seq(a₂ − 1)) ≠ 6   ∨   (page(seq(a₂ − 1)) = 0  ∧  16 ≤ x(seq(a₂ − 1)) < 181)   ∨   EntryAt(L₅, seq a₂)     （フィールド、狭めた）
```

`no_enter`: `SideFrame.entry_right_of_left` によると、入るフレームは、横の土管のルーチンを書く前に、`xLo` 以上の位置で `Q` に来ます。`subs_left` によると、このフレームは `xLo` より左でしか `Q` に来ません。`Run.coin₂` は `k = a₂ − 1` をとります。部屋の入るフレーム（`room.enters`）はこのフレームです（`Run.rt₂` と同じ）。`Run.buf₂` は `buffer₂` の真ん中の場合に `Run.coin₂` を使います。

Lean: `Theorems/BufferCoin.lean`（`bitP`、`MP`、`zoneM`、`preZ`、`walkG`、`posLeft`、`keyG`、`normG`、`optsG`、探索、`walkCheckG`、`rangePieces`、`rangeCover`、`mpOf`、`ref6x`、`knownG`、`startG`、`walkAll`、`searchOfG2`、`cfgOfG2`、`walkCheckG2`、`walkOKG_of_check2`、`cov_bitP`、`cov_zoneM`、`cov_preZ`、`LiveG`、`InTab`、`cover_liveG`、`live_stepG`、`subs_of_walkG`、`WalkOKG`、`walkOKG_of_check`、`left_of_posLeft`、`subs_left`、`coinCheck`、`cond_piece`、`no_enter`、`FactsB`）、`Theorems/Route.lean`（`RoomChecks.buffer`、`Run.buffer₂`、`Run.coin₂`、`Run.buf₂`）、非公開の `Proof/BufferCoin.lean`（`buffer_coin_check`。`Main.lean` の `genBufferCoin`）。`FactsB` は `BufferControl` からここへ移り、フィールド `coin` と `side` が増えました。公開ファイルにゲームのデータはありません。

## しくみ

**動きは短い.** 動きのルーチンは、速さの上位 4 ビットを符号つきで、桁上がりと一緒に位置に足します。だから速さのバイトのどの値でも、位置は −8 から 8 px しか動きません。つたのぼりのルーチンは表の 4 つの値の 1 つを足します。−14 から 14 px です。`Q` の前に位置を書くものはほかにありません。16 から 180 px からなら、`Q` の位置はページ 0 の 2 から 194 px で、`xLo` より左です。

**抽象機械は、すべてのビットが分かっているときだけバイトを足せます.** そこで歩きは、動きに要るところでバイトを値に分けます（`zoneM`）。

* 速さの上位ビットと 8 の比べ: アキュムレータのビット 3（分けないと、足すバイトが 2 つの範囲のどちらか、抽象の比べでは分かりません）。
* 足すバイトと 0 の比べ: アキュムレータ（抽象の比べは全部のビットが分かっているときだけ引けます。分けないと、符号のバイトが足すバイトと合いませんでした）。
* 位置への足し算: 桁上がり、足すバイト、アキュムレータ。
* つたのぼりの足し算: アキュムレータ。

だから足した後の位置は分かります。`Q` ではどの状態も表のものでなければなりません（`walkG`）。確認はそのそれぞれに `posLeft` を求めます。スクロールの処理の始めで、探索は位置を忘れます。そこでフレームの残りは [画面のバッファ](d-2-5-5-EntryBuffer-ja.md) の歩きと同じです。

**探索（証明の一部ではない）.** キーは位置、ページ、制御を持ちます。動きのルーチンの中と、つたのぼりのルーチンの書き込みでは、アキュムレータと足すバイトも持ちます。持たないと、探索は区間をまた合わせてしまいます。部屋のキーはこれらのバイトの上に置きます（2⁴⁸ 倍）。`keyY` の古いやり方では、部分が重なることがありました。

**なぜ歩きを `Q` で止めるか.** 最初の設計では、衝突のルーチン全体で位置を分かったままにしました。最初の区間が終わる前に 19 GB を超えました。分かった位置がほかのバイト（足すバイト、スクロールの量、当たりの箱）に広がり、状態を分けたままにするからです。この設計は、動きから `Q` までだけ位置を追います。

**大きさ.** 区間ごとに約 120 万から 133 万ステップ、失敗 0、状態 16.3 万から 19.7 万、`Q` の状態 91 から 2,170 個、すべてページ 0 で `xLo` より左です。プログラムでは、探索はそれぞれ約 8 から 9 秒、最大 735 MB。7 区間すべての確認はネイティブで 185 秒です。数秒より長いです。

**ラウンド 25: 表を 1 つに.** 7 つの歩きは、今は 1 つの探索と 1 つの表を共有します（`startG`、`walkAll`、`searchOfG2`、`cfgOfG2`、`walkCheckG2`、`walkOKG_of_check2`。`walkA` はなくなりました）。すべての区間の 14 の始めの状態からの探索: 2,002,560 歩、363,068 状態、失敗 0、18.8 秒。確認 `coinCheck` はネイティブで 87 秒（表 7 つでは 185 秒）。変わったのは `coinCheck` の中身（表 1 つ）で、`no_enter` の主張は同じです。

## 測ったこと（定理ではない）

`buffer-ctl-check FM2 300 real`（終了コード 0）: 映像の部屋と、部屋の映像のフレームからの自前の走り 1,200 本（種類 0 と 1、小さいのと大きいの、それぞれ 300 本。種類 1 は入口の前の最後の 60 フレームから始まり、土管の隣のコインを取る）。

| 走り | フレーム | 入口 | コインのフレーム（終わりの制御 6） | そのうちページ 0 の 16 から 180 px で終わるもの | そこで制御 6 で始まるフレーム | そのうち入るもの |
|---|---|---|---|---|---|---|
| 映像 | 111 | 1 | 13（52 から 163 px で終わる） | 13 | | |
| 種類 0、小 | 125,891 | 102 | 1,019 | 1,019 | 1,055 | 0 |
| 種類 0、大 | 113,761 | 126 | 1,229 | 1,229 | 1,265 | 0 |
| 種類 1、小 | 66,202 | 218 | 1,178 | 1,178 | 1,253 | 0 |
| 種類 1、大 | 69,677 | 208 | 1,245 | 1,245 | 1,320 | 0 |

制御 6 で始まる入るフレームはありません（`buffer₂` の最初の場合が 655 の入口すべてで成り立つ）。コインのフレームは最大 173 px で終わります。

`buffer-ctl-check FM2 0 coin`（終了コード 0）: 7 つの探索、上のとおり。`buffer-ctl-check FM2 1 coin` は `coinCheck` も走らせます（true）。

## ほかの部の使用

* パート c: `SideFrame.entry_right_of_left`、`SideFrame.frame_before` と非公開の `side_frame_check`（1-1-c-7-16）。`RoomMap.cond_of_rows`、`RoomMap.start_of_rowsF`、`RoomMap.clean_of_rows`、`RoomMap.map_of_rows`、`RoomMap.head_of_rows`。`Run.coin₂` を通して `room.enters`、`Run.roomEnter`、`EntryRoutine.rt_of_rows`、`chg.roomSites`、`ChangesBase.roomStay`。
* パート b: `ChangesK.run₁`、`PipeRunK.inRowsT`、`ChangesBase.ctlFirst₁`、`ChangesBase.ctl₁`。パート a: `Run.entry₁`。
* パート d: `EntryBuffer` の歩き（`hpB`、`knownB`）と `EntryHeight` の歩き（`preY`、`stepY`、`cov_preY`、`s_stepY`）、`BufferControl.Facts`。
* 循環はありません。どれも `buffer₂`、`Run.buf₂`、`Run.ctl₂`、`Run.coin₂` を使いません。

## 経路で変わったこと

* フィールドを狭めた: `buffer₂` に、入るフレームの始めの新しい真ん中の場合 `page = 0 ∧ 16 ≤ x < 181` が加わりました。古いフィールドから新しいフィールドが出ます。
* `RoomChecks.buffer : BufferCoin.FactsB …`（前は `EntryBuffer.Facts`。`FactsB` はここで新しく作ったもので、`EntryBuffer.Facts` にフィールド `ctl`、`coin`、`side` を加える）。`EntryHeight` の非公開ファイルの `buffer_facts` が作ります。
* 新しい定理 `Run.coin₂`。`Run.buf₂` がそれを使います。

## 仮定（Lean で証明していない）

* `buffer₂`: 入るフレームの前のフレームがコインを消したなら、そのフレームはページ 0 の 16 から 180 px で終わった（そうでなければ入口の 5 バイトは基準のもの）。これをなくすには、制御 6 で終わるフレームがそこで終わることを示します。そのコインは口より 3 列以上左にあるので、衝突のルーチンがコインを読むときの位置が要ります。ラウンド 25（[BufferEnd](d-2-5-5-3-BufferEnd-ja.md)、1-1-d-2-5-5-3）: 制御 6 で終わるフレームは 16 から 180 px で終わる（`Run.end₂`）ので、`buffer₂` が求めるのはそこでのページ 0 だけになりました。
* 部屋の各命令の `SiteOK`（`chg.roomSites`）、前と同じ。

**ファイル.** `Theorems/BufferCoin.lean`、`Theorems/Route.lean`、`Theorems/BufferControl.lean`（`ref_of_ne6` を加えた）。非公開の確認は `Proof/BufferCoin.lean`（`Main.lean` の `genBufferCoin`）。

**再現.**
```
.lake/build/bin/smbrta buffer-ctl-check FM2 0 coin       # 7 つの探索、約 1 分
.lake/build/bin/smbrta buffer-ctl-check FM2 1 coin       # coinCheck も、約 4 分
.lake/build/bin/smbrta buffer-ctl-check FM2 300 real     # 本物のフレーム、約 5 分
```
