[← Back](README-ja.md) | [English](d-2-4-2-11-HeadSide.md) | [Japanese](d-2-4-2-11-HeadSide-ja.md)

# 横の土管の位置の読みを、頭のマスから

**主張.** 部屋のすべてのフレームで、フレームの各命令がフィールド `roomRead` (頭のマスが地図で空いている、[頭の読みを地図の頭のマスから](d-2-4-2-10-HeadFree-ja.md)) を満たすなら、横の土管のコードが位置を読むところで位置の下のビットは 0 でない。だからフィールド `roomXbit` はなくなった: 入るフレームの `Xbit` は `roomRead` から出る。

これは証明した。ROM の検査を 1 つ足した (部屋のフレームの歩き、`HeadSide.checkX`)。検査は `LoopTime.recCheckB` の歩き (i) の一部なので、すでにある private の証明で証明される (`Proof.SiteMusic1`。新しい private のファイルはない)。フィールド `roomXbit` を取り除いた。足したフィールドはない。

`tr(j)` はフレームの `j` 命令後の機械、`x` は位置 (`Player_X_Position`)、`xAt` は横の土管によるその読み、`M` は地図。`SiteX` は `xbit` のない `SiteOK` ([横の土管の位置の読みは入るフレームだけ](d-2-4-2-9-SideRead-ja.md))。`ZeroIn`、`ReadIn`、`HeadFree` は [頭のマス](d-2-4-2-10-HeadFree-ja.md) と [読みでのタイル](d-2-4-2-8-ReadTiles-ja.md) のもの。`K_X` は、フレームの始めでの部屋の歩きの知っているビット (`RoomMusic.knownM`) と、プレイヤーの大きさのビット 1 から 7 (`SizeKeep`)。

## 命題

```
Xbit(m)        :=  pc(m) = xAt  →  x(m) & 15 ≠ 0                                       (SiteParts.Xbit)
xbitOK(A)      :=  pc(A) ≠ xAt  ∨  A は x & 15 の 1 のビットを 1 つ知っている              (1 つの状態の検査)

s_stepX        :  Sim(A, m),  SiteOK(m),  ZeroIn(m),  ReadIn(m),  HeadFree(m)   →   stepX(A) の後の状態の 1 つが step(m) を覆う
frame_of_walkX :  A₀ からの歩きが通る,  A₀ が m を覆う,  ∀ j: SiteX(tr j) ∧ ZeroIn(tr j) ∧ ReadIn(tr j) ∧ HeadFree(tr j)   →   ∀ j,  Xbit(tr j)
xbit_of_check  :  checkX,  RoomCond(r, K_X, m),  ∀ j: SiteX(tr j) ∧ ZeroIn(tr j) ∧ ReadIn(tr j) ∧ HeadFree(tr j)          →   ∀ j,  Xbit(tr j)
```

`Route.ChangesBase` で:

```
前     roomXbit : b₁ < a₂  →  ∀ j,  Xbit(tr_{a₂ − 1}(j))
今     (なし)
```

`LoopTime.loop_sites_of_rows` はもう `xlast` を取らない。フレーム `a₂ − 1` では `xbit_of_check` を使う: フレームの始めでの `K_X` つきの部屋の条件 (帰納法の `RoomCond` に大きさのビットを足したもの、`LoopTime.cond_size`)、各命令での 4 つの歩きからの `SiteX`、`ZeroIn`、`ReadIn` (`LoopTime.FrameOut`)、フィールド `roomRead` からの `HeadFree`。

## しくみ

横の土管のコードは、横の読みが横の土管のタイルを見つけ、プレイヤーが立っているときだけ走る。衝突のルーチンは、横のマスより前に頭のマスを、同じ位置で読む。下のビットが 0 の位置では、頭と横は同じ列にある。土管の列でそこに着地するプレイヤーの頭は、土管か床のマスにあり、`HeadFree` はそれを許さない。

歩きは [ブロックの地図](c-7-12-RoomMap-ja.md) の歩きと同じくフレーム全体をたどり、各命令の `SiteOK` を仮定にとる: 部屋の歩きからの `SiteX` と、命令を覆う状態での歩き自身の検査 `xbitOK` からの `Xbit` (`xbit_of_ok`)。切れとステップを足した:

* **位置.** 衝突のルーチンの入り口で、`x` の下のビットを 1 つずつ、最初の 1 まで (`lowBits`)。下の 4 ビットが 0 なら、上のビットとページの下のビットも (`highX`): するとどの読みの番地もわかる。頭と横の読みが横の土管の列にある 1 つの位置 (列の 16 倍、ページ 0) では、高さも (上の 4 ビットと、手本の入りの高さの行とその下の行での値、`yPieces`) とプレイヤーの大きさの下のビットも。大きさがないと、頭の検査の境界は歩きの知らない添え字で読まれ、歩きは頭の読みを飛ばしうる。
* **状態.** その位置では、プレイヤーの状態をルーチンの読みのところで、最初の 1 までビットごとに分ける。0 でない状態は 0 でないと知られたままなので、着地しないフレームは横の土管のコードに来ない。
* **ページと行.** キャリー 0 でのページの `ADC #0` で、アキュムレータはページを保つ (`EntryHeightBig.refineA`)。キャリー 1 で下のビットが 0 のオペランドの行の `SBC #` で、アキュムレータは下の 4 ビットを保つ (`refineS`。CPU のコードからの `sbc_low`)。だから読みの `Y` は下のビットが 0 で、値は高々 16 個。
* **読み.** ポインタがわかり `Y` の値が高々 16 個のブロックのバッファのルーチンの読み (`candRead`) で、ステップはどれかの番地が許すリストのタイルをそれぞれとる: 地図のバイトの外にビットを持たないブロックのバッファのバイト (`ZeroIn`)、頭の読みでは地図のバイトが頭のタイルのところだけ (`HeadFree`)。土管のマスでの頭の読みにはタイルがない: その切れに機械はない。
* **検査.** すべての状態が `xbitOK` を満たし、フレームの終わりもそう。

探索 (証明の一部ではない) は位置、ページ、高さ、状態、大きさをキーに入れ、横の検査の終わるところと衝突のルーチンの戻りでそれらを忘れる。256 個の位置をすべて分けた最初の探索は 6 GB を超えて止めた。その後の 2 つの探索は、位置 208 での横の土管の読みだけで失敗した: 1 つは分岐で「状態は 0 でない」を失い、1 つは大きさの 2 つの値を合わせていた。

## 測ったこと

`buffer-ctl-check FM2 N xwalk` (ネイティブ): 探索は 5,933,508 ステップ、433,074 の分かれ、失敗 0、表の状態 1,165,195、フレームの終わり 316、44 秒、3.9 GB。`N = 1` では `HeadSide.checkX` もネイティブで: 真、77 秒。`Proof.SiteMusic1` (この検査つきの歩き (i)) の private のビルドは、負荷 6 から 11 ほどの `prove.py` で 203 秒 (ラウンド 34: 72 秒)。ほかの 3 つの歩きのファイルは 80、311、117 秒で、private のビルドでいちばん長いファイルはいまも `Proof.SiteMusic3`。`#print axioms route_1_1` の名前はこのラウンドの前と同じ 304 個: 検査はすでにある `native_decide` の中にあり、CPU の `SBC` とビットの補題 (`sbc_nat`、`refineS_mem`、`xbit_of_mem`) は `bv_decide` を使わず `omega` と書き換えで証明した。

実際の走り: `buffer-ctl-check FM2 100 headfree` ([頭のマス](d-2-4-2-10-HeadFree-ja.md) のもの) では、横の土管の位置の読みは 195、196、198 px (小) と 195、196 px (大) で、同じフレームの頭のマスは列 12、土管の列の左だった。

## 証明していないこと

* `roomRead` (`HeadFree`) そのもの。このページはそれを入るフレームで使う。

## ほかの部分から使うもの

* 部分 c: `RoomMap.mapRef`、`RoomBlocks.readAddr_eq`、`readVal_eq`、`ptrZ`、`operand`、`tick_a`、`SideEntryRule.spots` (横の検査の出口、探索だけ)。
* 部分 d: `EntryHeightBig` (`ptrLo`、`ptrHi`、`refineA`、`adc0_a`、`AdcOK`)、`EntryHeight` (`Opts`、`routeY`、`mix64`、`heightI`)、`ScreenPage` (`preS`、`cov_preS`、`stepS`、`s_stepS`、`readStep`、`s_readStep`、`mem_tilesFor`、`sim_of_room`、`sim_clamp`)、`SizeKeep.sizeI`、`ReadTiles` (`ZeroIn`、`ReadIn`、`HeadFree`、`inBuf`)、`SideRead` (前のフレームの `no_xAt`)、`LoopTime` (`FrameOut`、`cond_size`)。
* 循環はない: フレーム `a₂ − 1` で歩きが使うのは、`Xbit` を使わない部屋の歩きからのそのフレームの `SiteX`、`ZeroIn`、`ReadIn` と、フィールド `roomRead`。
