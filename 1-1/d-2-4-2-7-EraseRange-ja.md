[← Back](README-ja.md) | [English](d-2-4-2-7-EraseRange.md) | [Japanese](d-2-4-2-7-EraseRange-ja.md)

# 境界からの消去の行

**主張.** 部屋のフレームの 4 つの歩きは、ラウンド 32 で示したこと（部屋のすべてのフレームでコインの消去はブロックのバッファの中に書くこと、`SiteOK` のほかの部分は残りのフィールドから）を、2 分の 1 から 3 分の 1 の表で示す。非公開のビルドは約 3 分の 1 になる。

これは証明した。フィールドは除かず、加えない。フレームの定理（`LoopTime.rec_frame1B` から `rec_frame4B`、`loop_sites_of_rows`）と `route_1_1` の文はラウンド 32 と同じ。変わったのは検査の中の歩きで、だから非公開の証明の表が変わった。

## ラウンド 32 が遅かったわけ

ラウンド 32（`EraseRow`）は衝突のルーチンでプレイヤーの高さ `y` を 9 つの切れに分け、ルーチンの戻りまで別々に保った。歩きのバイトはビットしか知らないので、`y ≤ 207` のような境界は、知っている上のビットがそれを含む切れの中にしかない。ラウンド 33 で歩き (ii) を測ると、239,141 の表の状態のうち 183,921 がその区間にあり、切れを除くとキーは 32,654 だけだった（キーごとに 5.6 状態）。歩き (iii) では 1,218,249 のうち 919,605 で、キーは 163,270。

## 命題

`tr_n(j)` はフレーム `n` の `j` 命令あとの機械。**境界**は 3 つの数 `(i, lo, hi)` で、バイト `i`（RAM のバイト、またはアキュムレータを表す `aI`）が `lo` 以上 `hi` 以下であること。歩きの抽象状態は境界のリストをフィールド `log` に持つ。`Sim`（抽象状態と機械の関係）は `log` を読まない。

```
FOK(l, m)       :=  ∀ (i, lo, hi) ∈ l,  lo ≤ val(m, i) ≤ hi          （val(m, aI) = m.a、ほかは RAM のバイト）
rlo(A, i), rhi(A, i) :=  A の知っているビットと A の境界のもとでのバイト i の最小と最大の値
range_ok        :  Sim(A, m) ∧ FOK(A.log, m)  →  rlo(A, i) ≤ val(m, i) ≤ rhi(A, i)

keepF_ok        :  Sim(A, m) ∧ FOK(l, m)  →  FOK(keepF(A, l), step(m))       （ステップが書かない RAM のバイトの境界: StepWrites.keepOK）
xferA_ok        :  Sim(A, m) ∧ FOK(A.log, m)  →  FOK(xferA(A), step(m))      （7 種類の命令でのアキュムレータの境界、下）
mkL_ok          :  Sim(B, m) ∧ FOK(B.log, m)  →  FOK(mkL(is, B), m)          （B の知っているビットからの新しい境界）
fok_of_leF      :  Sim(W, m) ∧ FOK(W.log, m) ∧ leF(W, D)  →  FOK(D.log, m)    （表の状態 D で覆うときは、その境界も求める）
covF_splitVal   :  Sim(A, m) ∧ FOK(A.log, m)  →  ∃ B ∈ splitVal(i, A), Sim(B, m)   （バイト i の境界の中の値）
```

`xferA` は、場所 `xq`（行の 7 つの命令）での `A` からの 1 ステップについて、`[lo, hi]` を `A` の中のアキュムレータの範囲として、次を与える:

```
LDA zp,X  （X を知っている）              a' ∈ [rlo(A, z + X), rhi(A, z + X)]
CLC, SEC                                  a' ∈ [lo, hi]
ADC abs,Y （Y、キャリー c を知る、ROM）    a' ∈ [lo + v + c, hi + v + c]          hi + v + c ≤ 255 のとき（v: オペランド）
AND #0xF0                                 a' ∈ [16 · ⌊lo/16⌋, 16 · ⌊hi/16⌋]
SBC #k    （キャリー c を知る）            a' ∈ [lo − (k + 1 − c), hi − (k + 1 − c)]   k + 1 − c ≤ lo のとき
STA zp                                    ram'(z) ∈ [lo, hi]
```

それぞれの場合は、その命令コードの CPU のコードから証明した（`step_rom`、`go_ldaZpx`、`go_adcAby`、`go_andImm`、`go_sbcImm`、`go_staZp`、`tick_a`、`tick_ram`）。

境界を持つ歩き（`walkV`）は、状態を分け（`piecesF`: 境界が除かない分けた切れ）、ラウンド 32 の歩きのステップ（`RoomPause.pstep`）を取り、各後続に境界を与える（`updF`: 保つもの、`xferA` のもの、`Rules.mkAt` の場所で知っているビットからの新しいもの。衝突のルーチンの戻りと消去のあとでは全部捨てる）。`frameV` は `EraseRow.frameG`（ラウンド 32）と同じ結論を持つ:

```
frameV  :  VOK(…) → RoomCond E r K m → InCls G m → (∀ j, R(tr j))  →  (∀ j, SiteOK P (tr j)) ∧ ∃ B, fin B ∧ Sim E (m.frame, 2) B (frame m i)
```

## しくみ

**高さのテスト.** 衝突のルーチンは `y` を 6 か所でテストする: 始め（`y < 207`）、頭の呼び出しの前（`y ≥` 頭の上の広がり）、足の呼び出しの前（`y < 207`）、プレイヤーが着地するところ（`y := y & 0xF0`）、横の呼び出しのそれぞれの前（`32 ≤ y < 228`、`8 ≤ y < 208`）。歩きは 6 か所を ROM のバイトから見つける（`windows`: 比べる命令が続く `y` の `LDA zp` と、ストアが続く `y` の `AND zp`）。それぞれで `y` をラウンド 32 の 9 つの切れに分け（`y` の境界で切り落とす）、比べる命令と分岐は各切れで決まる。窓のあとの場所で、歩きは切れの知っているビットから `y` の境界を作り、ビットを忘れる。だから切れはすぐにまた会う: その区間ではキーごとにほぼ 1 状態。

**行.** ブロックのバッファのルーチンは、行のオフセット `Y = ((y + adder) & 0xF0) − 32` を `LDA zp,X`、`CLC`、`ADC abs,Y`、`AND #0xF0`、`SEC`、`SBC #32`、`STA zp` で計算する。`xferA` は `y` の境界をこの 7 つの命令で動かし、ストアした行のバイトの境界にする。分けることはない。消去の前の行のバイトの `LDY zp` で、歩きはそのバイトを境界の中の値に分ける。だから消去で `Y` を知っていて、ラウンド 32 の検査 `eraseOK4` が成り立つ。この分け方は消去への道の上だけ。

**探索**（証明の一部ではない: 歩きが表を検査する）は、窓の切れを窓の中でだけ別々に保ち（`keyL`）、窓のあとの場所まで走らせ（`advAt`）、2 つの状態を合わせるときは 1 つめの各境界を 2 つめでも成り立つまで広げ（`joinV`）、消去のあとでアキュムレータと `Y` を忘れる（`aidsV`: そのあとのコードは読む前に両方を読み込む）。場所のリストは一度だけ作る（`Rules`、`KeyD`、`SplitD`）: ステップごとに見つけ直した最初の版は 2 倍の時間がかかった。

**測ったもの**（`buffer-ctl-check FM2 11 rangecheck` から `14`、ネイティブで、4 つを同時に、ほかの 3 人の作業と同時。探索だけの時間）:

| 歩き | 表（ラウンド 32、ラウンド 31） | 探索 | 失敗する状態 |
|---|---|---|---|
| (i) | 159,849（320,474、148,250） | 64 秒 | 0 |
| (ii) | 78,516（239,141、66,917） | 44 秒 | 0 |
| (iii) | 415,124（1,218,249、357,129） | 194 秒 | 0 |
| (iv) | 176,788（337,408、265,619） | 73 秒 | 0 |

非公開のビルド（最後の `prove.py` の段 5、ほかの作業のビルドと同時、負荷は約 4）: `Proof.SiteMusic1` 80 秒（ラウンド 32: 223 秒）、`SiteMusic2` 56 秒（196 秒）、`SiteMusic3` 236 秒（1,186 秒。静かな機械で約 820 秒）、`SiteMusic4` 84 秒（231 秒）。同じ時間帯にネイティブで、`LoopTime.recCheckB` の 4 つの歩きは合わせて 412 秒。ラウンド 32 の 4 つの歩きは 1,366 秒（`buffer-ctl-check FM2 1 rowcheck`）。

試して使わなかったもの: 行の読み込みで `y` を値に分けること（呼び出しごとに約 200 の切れ。表は同じくらい小さかったが、各切れを写して覆うのに時間がかかった）。探索で合わせた状態のドットを 64 から 2048 の倍数に丸めること（最後のドットの丸めは道に沿って積み重なり、時間の検査を壊す: 64 で 346 の失敗する状態。最初のドットだけの丸めは探索を長くした）。

## 仮定（Lean で証明していないもの）

* 新しいものはない。`roomRead` と `roomXbit` は変わらない。
* `roomXbit`（横の土管のコードが位置を読むとき、位置の下のビットが 0 でないこと）には、その読み込みで `x ≤ 207` px が要る: フレームをまたぐ境界（土管の口が壁になること）。歩きは `x` を知らない。入るフレームだけに狭めるには、`EntryRoutine.rt_of_rows` の歩き（`SideEntryEnd`、`SideEntryRest`、`RoomMap.clean_of_rows` を通る）をそれなしで言い直す必要がある。`x & 15 = 0` のとき、コードはエリアの切り替えのタイマーを設定しない。
* `roomRead` には、歩きの状態の中のブロックのバッファの中身が要る。消去のステップは、歩きがブロックのバッファのどのバイトも知らないことを求める（`bufFree`）。

## Lean

`Theorems/EraseRange.lean`: 境界（`mkF`、`fI`、`fLo`、`fHi`、`aI`、`valOf`、`abK`、`FOK`、`loOf`、`hiOf`、`rlo`、`rhi`、`okI`、`range_ok`、`mkL`、`keepF`、`leF`、`consF`）、CPU の 7 つのステップ（`tick_*`、`step_rom`、`go_mZpx`、`go_ldaZpx`、`go_fetch16`、`go_penalty`、`go_adcAby`、`go_andImm`、`go_sbcImm`、`go_staZp`、`add3_toNat`、`and_f0`、`not_toNat`）、`xferA`、`xferA_ok`、`Rules`、`updF`、`updF_ok`、分け方（`CovF`、`piecesF`、`cov_pieces`、`splitVal`、`covF_splitVal`、`splitV`、`covF_splitV`）、歩き（`stepV`、`coverV`、`weakenV`、`walkV`、`LiveV`、`live_stepV`、`frame_of_walkV`）、探索（`joinV`、`routeV`、`advV`、`runV`、`searchV`、`searchBV`、`cfgBV`）、検査（`walkCheckV`、`VOK`、`vok_of_check`、`frameV`）、ROM の上の `windows`、`merges`、`rowPcs`、`eraY`、`zPtr`、`SplitD`、`splitData`、`aidsV`、`rulesOf`、`forgetV`、`advAt`、`KeyD`、`keyL`、`keyData`。`Theorems/LoopTime.lean`: `walkChk` は `EraseRange.walkCheckV` を使う。`rec_frame1B` から `rec_frame4B` は `EraseRange.frameV` を使う（文は同じ）。非公開の証明の文はラウンド 32 と同じ。定理は公理 `propext`、`Classical.choice`、`Quot.sound` だけを使う。

## 再現

```
.lake/build/bin/smbrta buffer-ctl-check FM2 1 rangecheck     # 境界を持つ 4 つの歩き、ネイティブで（2 は recCheckB も走らせる）
.lake/build/bin/smbrta buffer-ctl-check FM2 13 rangecheck    # 歩き (iii) だけ（11、12、14: 歩き (i)、(ii)、(iv)）
```
