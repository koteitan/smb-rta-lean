[← Back](README-ja.md) | [English](d-2-5-5-3-BufferEnd.md) | [Japanese](d-2-5-5-3-BufferEnd-ja.md)

# コインを消したフレームは 16 から 180 px で終わる

**主張.** 部屋のフレームが、画面のバッファの制御 0 か 6 で始まり、制御 6 で終わるなら、ページ上の位置 16 から 180 px で終わります。証明しました。ROM の確認は 1 つです（部屋のフレームの歩き 2 つ、ネイティブで約 60〜80 秒）。そこでフィールド `buffer₂` が求めることはページだけになりました。入るフレームの前のフレームがコインを消したなら（そのとき制御は 6）、そのフレームはページ 0 で終わる、ということです。本物の走りでは部屋のページはいつも 0 です。いつもそうなることは証明していません。

名前は [部屋を通る画面のバッファの制御](d-2-5-5-1-BufferControl-ja.md) と [制御 6 で口より左から始まるフレームは入らない](d-2-5-5-2-BufferCoin-ja.md) のものです。`x(m)` と `page(m)` はプレイヤーのページ上の位置とページです。`Q` は動きの終わり（`PlayerSubs`）です。`r` は部屋の基準の機械（制御 0）、`r₆` は同じで制御を 6 にしたものです。`K_B = K_T ∪ { c のすべてのビット }` です。

## 主張の式

```
pieces       :=  [0, 16)、[16, 181)、[181, 256) をそろった区間に分けたもの                              （12 個。すべての値を覆う）
inside(a)    :=  区間 a のどの値も 16 から 180
finX(B)      :=  c が 6 でないと分かっている   ∨   inside(x の区間)
walkE(r')    :=  (r', K_B) からの歩きが通り、そのどのフレームの終わりも finX を満たす
endCheck     :=  walkE(r)  ∧  walkE(r₆)

end_frame    :  walkE(r'),   RoomCond(r', K_B, m),   ∀ j, SiteOK(tr(j)),   c(frame m i) = 6     →   16 ≤ x(frame m i) < 181
end_step     :  keepCheck,   endCheck,   RoomCond(r, K_T, m),   ∀ j, SiteOK(tr(j)),   c(m) ∈ {0, 6},   c(frame m i) = 6
                →   16 ≤ x(frame m i) < 181
end_of_rows  :  [b, a) で RoomMap.map_of_rows の条件,   keepCheck,   startCheckC,   endCheck,   b ≤ n < a,   c(seq(n + 1)) = 6
                →   16 ≤ x(seq(n + 1)) < 181

Run.end₂     :  c(seq(a₂ − 1)) = 6   →   16 ≤ x(seq(a₂ − 1)) < 181                                    （定理、新しい）
Run.buffer₂  :  c(seq(a₂ − 1)) ≠ 6   ∨   page(seq(a₂ − 1)) = 0   ∨   EntryAt(L₅, seq a₂)                （フィールド、狭めた）
```

`Run.end₂`: `a₂ − 1 = b₁` なら、そのフレームは部屋の始めで、制御は基準の 0 です（`BufferControl.start_ctl`）。そうでなければフレーム `a₂ − 2` は部屋のフレームで、`end_of_rows` が位置を与えます。`Run.buf₂`: ページ 0 で制御 6 なら、`Run.end₂` が 16 ≤ x < 181 を与え、`Run.coin₂`（ラウンド 24）によりそのフレームは入りません。

Lean: `Theorems/BufferEnd.lean`（`piecesX`、`piecesCover`、`inside`、`MX`、`zoneX`、`preX`、`finX`、`readAt`、`eraseOut`、`stepZ`、`walkX`、探索、`walkCheckX`、`piece_of_cover`、`cov_zoneX`、`cov_preX`、`s_stepZ`、`LiveX`、`cover_liveX`、`live_stepX`、`frame_of_walkX`、`WalkOKX`、`walkOKX_of_check`、`frame_endX`、`fin_spec`、`end_frame`、`findAbs`、`mxOf`、`hpX`、`walkE`、`endCheck`、`end_step`、`end_of_rows`、`FactsE`）、`Theorems/Route.lean`（`RoomChecks.buffer`、`Run.buffer₂`、`Run.end₂`、`Run.buf₂`）、非公開の `Proof/BufferEnd.lean`（`buffer_end_check`。`Main.lean` の `genBufferEnd`）。公開ファイルにゲームのデータはありません。

## しくみ

**どのコインも衝突のルーチンを終わらせる.** 頭、足、横の読み取りでコインが見つかると、コインを消す処理に行きます。消す処理は制御を 6 にし、そのあと衝突のルーチンから戻ります。横の衝突の押し戻しも、そこから戻ります。だからコインを消すフレームでは、動きの終わりのあと位置は書かれません。例外はスクロールの処理で、プレイヤーが画面の外にいると画面の端に置きます。

**位置を区間に分ける.** `Q` で歩きは位置を 12 個の区間に分けます。区間の分かっているビットは上のほうの続いたビットです。7 個が `[16, 181)` の中、5 個が外です。区間が中なら、ブロックバッファの読み取りは `SiteOK` の表のどのタイルでもよく、コインでもかまいません。そのとき区間はフレームの終わりまで残り、そこで `finX` が成り立ちます。

**区間が外なら、読み取りの場所が分かる.** 抽象機械はバイトの足し算を、すべてのビットが分かっているか、どれも分からないかでしか行いません。そこで歩きは、区間が外のときだけ、次の場所で分けます（`zoneX`）。

* 足すものの番号を読むところで、番号のビット（番号は 3 つのどれか: 大きいプレイヤー、水の中の大きいプレイヤー、小さいかしゃがんだプレイヤー）;
* ブロックバッファのルーチンがプレイヤーの位置を足すところで、位置をその値に;
* ブロックバッファの番地を作るルーチンの始めで、ページのビット（ページは分かっていない）;
* 行のマスクで、アキュムレータの上のビット。

すると読み取りのポインタと `Y` が分かります。新しい一歩 `stepZ` は、そのような読み取りで、`SiteOK` の表のタイルのうち、読むバイトの分かっているビットに合うものを一つずつ与えます（部屋の条件は、マップで 0 のビットを知っています）。マップでコインになりうるバイトは 1 つめのブロックバッファにしかなく、4 から 10 の列の 19 マスです。位置が外なら読み取りの列は 0、1、11 から 15 なので、コインは読まれません。

**ブロックバッファの外の読み取り.** 行の分け方は、本当のコードが読まない行も出します（高さは読み取りの前に調べられますが、抽象機械はそれを覚えません）。ページのビットが 1 のそのような読み取りは、2 つめのブロックバッファの先の RAM を読みます。歩きはそこを知らないので、コインが読まれることがあります。そのときコインを消す処理はそこに書きます。`SiteOK` によると、消す処理はブロックバッファの中に書きます。そこで `stepZ` は、場所が分かっていてブロックバッファの外にある消す処理では、機械を持ちません（`eraseOut`）。

**探索（証明の一部ではない）.** キーには制御と位置の区間があります。区間が外なら、ブロックバッファのルーチンと番地のルーチンの中で、キーにレジスタ、ポインタ、行、和も入れます。読んだバイトがコインでありうる間は、ポインタと行を残します。位置を足したあと、状態は位置の値を区間まで、和を上のビット（列）まで忘れます。タイルを保存したあと、タイルがコインでありえなければ、ポインタ、行、`Y` を忘れます。衝突のルーチンから戻るとき、制御が 6 でないと分かっていれば位置を忘れます。これらがないと、探索は一度 26.8 GB を超えました（止めました）。

**大きさ.** 制御 0 からの歩き: 1,218,211 歩、311,882 状態、失敗 0、14.6 秒。制御 6 から: 1,776,901 歩、373,444 状態、失敗 0、21.3 秒。最大 1.9 GB。制御が 6 でありうるフレームの終わりは、中の区間だけです。2 つの歩きの確認はネイティブで 68 秒です。数秒より長くかかります。

## 測ったこと（定理ではない）

`buffer-ctl-check FM2 300 real`（exit 0）: 動画の部屋と、動画の部屋のフレームから始めた自分の走り 1,200 本（種類 0 と 1、小さいのと大きいの、各 300。種類 1 は入口の前の最後の 60 フレームから始め、土管の近くのコインを取る）。

| 走り | フレーム | 入口 | コインのフレーム（終わりに制御 6） | そのうち 16 から 180 px で終わるもの（どのページでも） | 新しい `buffer₂` が成り立つ入口 |
|---|---|---|---|---|---|
| 動画 | 111 | 1 | 13（52 から 163 px で終わる） | 13 | 1 |
| 種類 0、小さい | 125,891 | 102 | 1,019 | 1,019 | 102 |
| 種類 0、大きい | 113,761 | 126 | 1,229 | 1,229 | 126 |
| 種類 1、小さい | 66,202 | 218 | 1,178 | 1,178 | 218 |
| 種類 1、大きい | 69,677 | 208 | 1,245 | 1,245 | 208 |

コインのフレームは最大 173 px で終わります。消したあと、フレームの終わりまで位置は変わりません。これらの走りのどのフレームもページ 0 で始まります。入るフレームは制御 0 で始まります（`buffer₂` の最初の場合）。`entry-height-check FM2 50 real`（exit 0）は 41 の入口で新しい `buffer₂` を数えます。すべて成り立ちます。

`buffer-ctl-check FM2 0 end`（exit 0）: 上の 2 つの探索。`buffer-ctl-check FM2 1 end` は `endCheck` も走らせます（true、68 秒）。

## 他の部分から使うもの

* 部分 c: `RoomMap.cond_of_rows`、`RoomMap.MapFacts`、`RoomMap.startCheckT`、`chg.roomSites`（`SiteOK`: 読み取りのタイルの表と消す場所）、`ChangesBase.roomStay`、`Run.b₁_lt_a₂`。`RoomBlocks.readAddr_eq`、`readVal_eq`、`writeAddr_eq`、`ptrZ`、`operand`。
* 部分 b: `ChangesK.run₁`、`PipeRunK.inRowsT`、`ChangesBase.ctlFirst₁`、`ChangesBase.ctl₁`。部分 a: `Run.entry₁`。
* 部分 d: `BufferControl`（`keepCheck`、`keep_parts`、`cond0`、`cond6`、`ref6`、`ctl_of_rows`、`startCheckC`、`start_ctl`）、`EntryBuffer`（`hpB`、`knownB`、`ctlI`）、`EntryHeight`（`preY`、`stepY`、`cov_preY`、`s_stepY`）、`EntryHeightBig`（`ptrLo`、`ptrHi`、`readAd`、`readI`）、`BufferCoin`（`rangePieces`、`FactsB`、ルートでは `Run.coin₂`）。
* 循環なし: これらのどれも `buffer₂`、`Run.buf₂`、`Run.end₂` を使いません。

## ルートで変わったこと

* フィールドを狭めた: `buffer₂` から位置がなくなりました。ラウンド 24: `c ≠ 6 ∨ (page = 0 ∧ 16 ≤ x < 181) ∨ EntryAt`。今: `c ≠ 6 ∨ page = 0 ∨ EntryAt`。どれも入るフレームの始めです。古いフィールドから新しいものが出ます。
* `RoomChecks.buffer : BufferEnd.FactsE …`（前は `BufferCoin.FactsB`。`FactsE` はそれにフィールド `ends : endCheck = true` を足したもの）。非公開の `EntryHeight` のファイルの `buffer_facts` が作ります。
* 新しい定理 `Run.end₂`。`Run.buf₂` がそれを使います。

## 仮定（Lean で証明していないこと）

* `buffer₂`: 入るフレームの前のフレームがコインを消したなら、そのフレームはページ 0 で終わる（そうでなければ入口の 5 バイトは基準のもの）。これをなくすには、部屋のどのフレームでもページが 0 であることを証明します。動きと押し戻しはページに繰り上がるので、部屋のどのフレームでも、壁の近くでも、位置が要ります。
* 部屋のどの命令でも `SiteOK`（`chg.roomSites`）。前と同じです。

**ファイル.** `Theorems/BufferEnd.lean`、`Theorems/Route.lean`。非公開の確認は `Proof/BufferEnd.lean`（`Main.lean` の `genBufferEnd`）。

**再現のしかた.**
```
.lake/build/bin/smbrta buffer-ctl-check FM2 0 end        # 探索 2 つ、約 40 秒
.lake/build/bin/smbrta buffer-ctl-check FM2 1 end        # と endCheck、約 2 分
.lake/build/bin/smbrta buffer-ctl-check FM2 300 real     # 本物のフレーム、約 5 分
```
