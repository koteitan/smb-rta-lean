[← Back](README-ja.md) | [English](d-2-4-2-9-SideRead.md) | [Japanese](d-2-4-2-9-SideRead-ja.md)

# 横の土管の位置の読みは入るフレームだけ

**主張.** 部屋の、入るフレームより前のどのフレームでも、横の土管のコードはプレイヤーの位置を読まない。だからフィールド `roomXbit`（その読みで位置の下のビットが 0 でない）は入るフレーム `a₂ − 1` でだけ求める。

これは証明した。ROM の検査はすでにある非公開の証明の中にある（`LoopTime.recCheckB` の 4 つの歩き。新しい非公開のファイルはない）。フィールド `roomXbit` を狭めた。フィールドは加えない。

`tr_n(j)` はフレーム `n` の `j` 命令あとの機械。`xAt` は横の土管が位置を読むところ（`PlyrPipe` の位置の `LDA`）、`stAt` はそのあとのルーチンのバイトのしまい（`xAt` から最初のルーチンのバイトの `STA zp`）、`rt(m)` はルーチンのバイト、`v` は参照のルーチン（プレイヤーのルーチン）。`a₂` は部屋の最初の制御 `b₁` から、プレイヤーのルーチンでないルーチンで始まる最初のフレーム。

## 命題

```
Xbit(m)      :=  pc(m) = xAt  →  x(m) & 15 ≠ 0                                       （SiteParts.Xbit、前と同じ）
XInv(j)      :=  (∃ k ≤ j, pc(tr k) = xAt)  →  xAt ≤ pc(tr j) ≤ stAt  ∨  rt(tr j) ≠ v

xinv_step    :  rtOK(A), wsetOK(A), Sim(A, tr j), SiteX(tr j), XInv(j)   →   XInv(j + 1)
no_xAt       :  ∀ j, XInv(j)、フレームは終わった、¬(xAt ≤ pc(frame) ≤ stAt)、rt(frame) = v   →   ∀ j, pc(tr j) ≠ xAt
```

抽象状態 `A` 1 つの検査:

```
rtOK(A)    :=  (pc(A) ≠ stAt  ∧  （A のステップはルーチンのバイトを保つ  ∨  A はコインの消去にある））
               ∨  A はルーチンのバイトの STA zp で、割り込みでなく、アキュムレータを知っていて ≠ v
wsetOK(A)  :=  ¬(xAt ≤ pc(A) < stAt)  ∨  A からの歩きのステップのどの後続 B も xAt ≤ pc(B) ≤ stAt
finX(B)    :=  ¬(xAt ≤ pc(B) ≤ stAt)                 （歩きのフレームの終わり）
```

`Route.ChangesBase` でフィールドが変わる:

```
前     roomXbit : ∀ n ∈ [b₁, a₂), ∀ j,  Xbit(tr_n(j))
今     roomXbit : b₁ < a₂  →  ∀ j,  Xbit(tr_{a₂ − 1}(j))
```

## しくみ

**読みで仮定がない.** 歩きのステップは `xAt` で位置を、下のビットが 1 つ立つ 4 つの切れに分けていた（`ScreenPage.preS`）。それには `Xbit` が要る。部屋のフレームの歩きは今は `EraseRange.pstepX` を使う。`xAt` で 5 つめの切れは下の 4 ビットが 0（`preSX`）。その道ではコードはエリアの切り替えのタイマーを置かず、ルーチンのしまいへ進む。ステップは `SiteX`、`SiteOK` のほかの 5 つの部分だけを要る（`s_pstepX`。ステップのほかの関数は `xAt` を見ないので、`xAt` を機械の場所から動かすと `SiteX` は `SiteOK` になる、`siteOK_movX`）。4 つの歩きは各フレームの各命令で `SiteX` を示す。

**読みからルーチンのしまいまで.** `xAt` からコードは下のビットをテストし、タイマーを置くかもしれず、ルーチンのバイトを読み、2 つのルーチンと比べ、横の土管のルーチンをしまう。歩きはそこでルーチンのバイト（プレイヤーのもの）を知っているので、どの分岐もこのコードを出ない。`wsetOK` は、`xAt` から `stAt` の前までの状態のどの後続も `xAt` から `stAt` にあることを検査する（歩きのステップの後続のどれかが次の機械を覆う: `EraseRange.succ_of`）。`stAt` でしまいはプレイヤーのルーチンでない知られた値を書く。`rtOK` は、ほかのどのステップもルーチンのバイトを保つか、プレイヤーのルーチンでない値を書くことを検査する（コインの消去はブロックのバッファに書き、それはルーチンのバイトより上にある）。だから `xAt` のあと機械は `xAt` から `stAt` にあり、しまいのあとはルーチンのバイトがプレイヤーのものでない（`XInv`、`ReadTiles.frame_of_walkVI` が運ぶ命令の番号の不変条件）。

**順のフレーム.** 歩きのフレームは `xAt` から `stAt` の外で終わる（歩きの終わりの検査の `finX`）。`n + 1 < a₂` のフレーム `n` はプレイヤーのルーチンで終わる（`a₂` の定義）。だから `xAt` を走らせず（`no_xAt`）、そのフレームで `Xbit` は示すことなく成り立つ。フレーム `a₂ − 1` ではフィールドがそれを与える。`LoopTime.loop_sites_of_rows` が `SiteX` と `Xbit` を合わせて `SiteOK` にする。

## 測ったこと

`buffer-ctl-check FM2 N tilecheck`（ネイティブ、`PLACE/git` から）: 5 つめの切れと、このページと [読みでのブロックのバッファのタイル](d-2-4-2-8-ReadTiles-ja.md) の検査つきの 4 つの歩き。

| 歩き | 表（5 つめの切れの前） | `xAt` から `stAt` の状態 | 失敗する表の状態 | 失敗する始まり |
|---|---|---|---|---|
| (i) | 159,889 (159,849) | 104 | 0 | 0 |
| (ii) | 78,556 (78,516) | 104 | 0 | 0 |
| (iii) | 415,324 (415,124) | 520 | 0 | 0 |
| (iv) | 176,828 (176,788) | 104 | 0 | 0 |

このページとタイルの検査つきの非公開のビルド（最後の `prove.py`、負荷は約 6 から 9）: `Proof.SiteMusic1` 72 秒、`SiteMusic2` 51 秒、`SiteMusic3` 272 秒、`SiteMusic4` 81 秒（ラウンド 33: 負荷約 4 で 80、56、236、84 秒）。ネイティブで `LoopTime.recCheckB` は真。

実際の走り（`buffer-ctl-check FM2 1100 loopreal`、ラウンド 34、ラウンド 32 と同じ）: `xAt` での位置の読みは 612 回（ムービーで 1、自分の走りで 316 と 295）、すべて 195 から 197 px で、下の 4 ビットが 0 のものはない。`rtOK` の最初の版はコインの消去を許さず、消去でだけ失敗した（歩き (i)、(ii)、(iv) の 20 の表の状態）。

## ほかの部分から使うもの

* パート c: `RoomBlocks.erase_other`、`zI`。
* パート d: `RoomPause.pstep` の部分（`keepP`、`inP`、`keepP_ok`、`sim_keepBits`、`sim_keep0`、`keepBits_k`、`ph_of_spent`）、`EraseRange`（境界つきの歩き、`step_rom`、`go_staZp`、`tick_ram`）、`ScreenPage`（`preS`、`cov_preS`、`or_bit_of`、`s_stepS`、`sim_clamp`、`findOpZ`）、`StepWrites`（`keepOK`、`keep_step`、`s_pstep` の部分）、`ReadTiles.frame_of_walkVI`。
* `Route`: `a₂` の定義（`ChangesBase.roomStay`: `[b₁, a₂)` の各フレームはプレイヤーのルーチンで始まる）。`ChangesK.roomSites` がすでに使う。
* 循環はない: フレーム `n` の `no_xAt` は、フレーム `n` の歩き（`Xbit` でなく `SiteX` で）と、`a₂` の定義からのフレーム `n + 1` の始まりを使う。

## 証明していないこと

* 入るフレームでの `roomXbit`: そこで横の土管のコードが位置を読むとき、位置の下のビットは 0 でない。測った走りでは読みは 195 から 197 px。下のビットが 0 なのは 208 px だけ。証明には、いくつものフレームにわたる位置の上限（壁としての土管の口）が要る。

## Lean

`Theorems/SideRead.lean`: `stAtOf`、`rtOK`、`wsetOK`、`finX`、`XInv`、`rt_step`、`wset_step`、`xinv_zero`、`xinv_stop`、`xinv_step`、`no_xAt`、`xChk`、`xFacts`。`Theorems/EraseRange.lean`: `SiteX`、`siteX_of`、`siteOK_of_X`、`movX`、`ne_add_one`、`siteOK_movX`、`placesOK_movX`、`stepS_movX`、`keepP_movX`、`preSX`、`andF0_all`、`andF0_of`、`cov_preSX`、`baseSX`、`s_baseSX`、`pstepX`、`s_pstepX`、`succ_of`。`stepV` は `pstepX` を使い、`live_stepV`、`frame_of_walkV`、`frameV` は `SiteX` を与える。`Theorems/ReadTiles.lean`: `frame_of_walkVI` と `frameVI` は命令の番号の不変条件 `J` を運び、フレームの終わりを与える。`Theorems/LoopTime.lean`: `chk1X`、`chk2X`、`chk4X`、`finAnd`、`spR`、`stR`、`rtR`（歩きはこれを使う）、`XInvR`、`xJ_of`、`xJs_of`、`xJ0_of`、`FrameOut`、`pcOut_of`、`walk1B_x`。`RestU` と `RestB` は `xbit` を持たない。`rec_frame1B` から `rec_frame4B` は `FrameOut` を与え、`loop_sites_of_rows` はフレーム `a − 1` でだけ `Xbit` を求める（`xlast`）。`Theorems/Route.lean`: フィールド `roomXbit`。

## 再現

```
.lake/build/bin/smbrta buffer-ctl-check FM2 2 tilecheck      # 5 つめの切れと検査つきの 4 つの歩き、そのあと recCheckB と startCheckT をネイティブで
.lake/build/bin/smbrta buffer-ctl-check FM2 1100 loopreal    # 実際のフレームでの位置の読み
```
