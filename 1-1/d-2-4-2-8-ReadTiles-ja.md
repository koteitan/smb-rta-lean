[← Back](README-ja.md) | [English](d-2-4-2-8-ReadTiles.md) | [Japanese](d-2-4-2-8-ReadTiles-ja.md)

# 読みでのブロックのバッファのタイル

**主張.** 部屋のすべてのフレームのすべての命令で、ブロックのバッファのルーチンの読みはリストのタイルを読む。部屋のフレームの歩きはこれを 2 つの事実から示す。2 つのブロックのバッファのどのバイトもリストのタイルであること、そして読みのアドレスがブロックのバッファの中にあること。だからフィールド `roomRead` は頭の半分だけを求める。頭のための読みは空のタイルかコインを返す。

これは証明した。ROM の検査はすでにある非公開の証明の中にある（`LoopTime.recCheckB` の 4 つの歩きと `RoomMap.startCheckT`。新しい非公開のファイルはない）。フィールド `roomRead` を狭めた。フィールドは加えない。

ラウンド 35: フィールド `roomRead` は頭のために読むバイトをもう求めない。頭のマスが地図で空いていることだけを求める。歩きは地図のビットも運び、読むバイトはそこから出る（[頭の読みを地図の頭のマスから](d-2-4-2-10-HeadFree-ja.md)）。

`tr_n(j)` はフレーム `n` の `j` 命令あとの機械。`B` は 2 つのブロックのバッファの 416 バイトの集合、`T` はタイルのリスト（`P.tiles`: 参照の機械のブロックのバッファのタイルと空のタイル。この ROM では 12 個）。`read` はブロックのバッファのルーチンの `LDA (zp),Y`、`addr(m)` はそのアドレス、`val(m)` は読むバイト、`save(m)` はルーチンがオフセットを置くバイト、`heads` は頭のオフセット、`T_head` は空のタイルとコイン。`m(d)` は `m` の RAM のバイト `d`。

## 命題

```
TilesIn(m)  :=  ∀ d ∈ B,  m(d) ∈ T
ReadIn(m)   :=  pc(m) = read  →  addr(m) < 0x2000  ∧  (addr(m) & 0x7FF) ∈ B
ReadH(m)    :=  pc(m) = read  →  save(m) ∈ heads  →  val(m) ∈ T_head
Read(m)     :=  pc(m) = read  →  val(m) ∈ T  ∧  (save(m) ∈ heads → val(m) ∈ T_head)          （SiteParts.Read、前と同じ）

read_of        :  TilesIn(m) ∧ ReadIn(m) ∧ ReadH(m)  →  Read(m)
tiles_step     :  0 ∈ T,  Sim(A, m),  keepOKB(A),  SiteX(m),  TilesIn(m)   →   TilesIn(step(m))
                  (SiteX(m) は SiteOK(m) から位置のビットの部分を除いたもの（1-1-d-2-4-2-9）)
readIn_of_ok   :  Sim(A, m),  FOK(A.log, m),  readInOK(A)   →   ReadIn(m)
tiles_of_rows  :  startCheckT,  InRowsT(m),  control(m)   →   TilesIn(m)
frameVI        :  不変条件 I つきの frameV:  I(tr 0),  （各状態の検査と I(tr j)  →  I(tr (j + 1))）   →   ∀ j, I(tr j)
```

抽象状態 `A` 1 つの検査:

```
keepOKB(A)   :=  A のステップは B のどのバイトも書かない  （StepWrites.keepOK）
                 ∨  A はコインの消去にあり、割り込みでなく、オペランドは ROM にあり、A はアキュムレータ = 0 を知っている
readInOK(A)  :=  pc(A) ≠ read
                 ∨  ポインタの上のバイト h を知っていて、256·h + 510 < 2048、
                    bufLo ≤ 256·h + min(l)、   256·h + max(l) + max(Y) < bufLo + |B|
```

`l` は `A` が知っているポインタの下のバイト、`max(Y)` は `A` の知っているビットと境界のもとでの `Y` の最大（`yI` の `EraseRange.rhi`）。

`Route.ChangesBase` でフィールドが変わる:

```
前     roomRead : ∀ n ∈ [b₁, a₂), ∀ j,  Read(tr_n(j))
今     roomRead : ∀ n ∈ [b₁, a₂), ∀ j,  ReadH(tr_n(j))
```

## しくみ

**タイルは残る.** 部屋の最初の制御で、部屋への切り替えの行はブロックのバッファのすべてのバイトを知っている（416 のうち 416）。`RoomMap.startCheckT` は、行の制御のある各状態で `B` のどのバイトも知られていて `T` のタイルであることも検査する（`tileRow`）。行は両方の検査のために 1 回だけ計算する。そして各ステップは `TilesIn` を保つ。`B` のどのバイトも書かないステップはすべてを保つ。コインの消去 `STA (zp),Y` はアキュムレータをそのアドレスに書き（`erase_ram`、その命令コードの CPU のコードから）、そこでのアキュムレータは 0 で、空のタイルであり `T` にある。4 つの歩きは着くすべての状態で `keepOKB` を検査する。だから `TilesIn` はフレームのすべての命令とその終わりで成り立つ。

**不変条件つきのフレーム.** `EraseRange.frame_of_walkV` は命令を 1 つずつ進む。`ReadTiles.frame_of_walkVI` も同じで、機械の不変条件 `I` を運ぶ。命令 `j` で歩きの状態は `tr(j)` を覆い、その検査が成り立ち、`I(tr(j))` と検査から `I(tr(j + 1))` が出る。`SiteOK(tr(j))` を出す検査は `I(tr(j))` を使ってよい。`I = TilesIn` とすると、`Read(tr(j))` は `TilesIn(tr(j))`、読みでの検査 `readInOK`、フィールド `ReadH` から出る。フレームの帰納法（`LoopTime.loop_sites_of_rows`）は `TilesIn` を 1 つのフレームの終わりから次のフレームの始めへ運ぶ。

**読みのアドレス.** ルーチンは行 `Y = ((y + adder) & 0xF0) − 32` を計算し、しまい、`TAY` で `Y` に写し、`LDA (zp),Y` で読む。ラウンド 33（`EraseRange`）は高さの境界を行の命令を通してアキュムレータの境界に移した。今は行の `STA zp` がアキュムレータの境界を保ち、`TAY` がその境界を `Y` に渡す（`xferY`、2 つの命令コードの CPU のコードから証明。`Y` は境界の新しいバイト `yI`）。読みで歩きはポインタのページ、その下のバイトの最大の値、`Y` の境界を知っていて、`readInOK` が成り立つ。

## 測ったこと

`buffer-ctl-check FM2 N tilecheck`（ネイティブ、`PLACE/git` から）: 新しい検査つきの 4 つの歩き。

| 歩き | 表（ラウンド 33） | 失敗する表の状態 | 失敗する始まり |
|---|---|---|---|
| (i) | 159,889 (159,849) | 0 | 0 |
| (ii) | 78,556 (78,516) | 0 | 0 |
| (iii) | 415,324 (415,124) | 0 | 0 |
| (iv) | 176,828 (176,788) | 0 | 0 |

このページの検査だけのとき、表の大きさはラウンド 33 と同じだった（159,849、78,516、415,124、176,788）。`Y` とアキュムレータの新しい境界は `TAY` と読みにだけあり、読みに表の状態はない。上の数は [横の土管の読み](d-2-4-2-9-SideRead-ja.md) もあるとき（その 5 つめの切れで 40 から 200 状態ふえる）。マップのブロックのバッファのどのバイトもリストのタイル（416 バイト、リストの外は 0）。非公開のビルド: [横の土管の読み](d-2-4-2-9-SideRead-ja.md) を見よ（同じ 4 つのファイル、最長 272 秒）。実際の走り（`loopreal`、ラウンド 34、ラウンド 32 と同じ）: 3,946,790 回の読み、ブロックのバッファの外は 0、リストにないタイルは 0、頭の読みで頭のリストの外は 0。

## ほかの部分から使うもの

* パート c: `RoomMap`（`startCheckT` の行、`InRowsT`）、`RoomBlocks.readAddr_eq`、`readVal_eq`、`ptrZ`、`operand`、`zp_lt`、`tick_y`。
* パート b: `ChangesK.run₁`、`PipeRunK.inRowsT`、`ChangesBase.ctlFirst₁`、`ChangesBase.ctl₁`（`ChangesK.roomSites` がすでに使う）。
* パート d: `EraseRange`（境界つきの歩き）、`LoopTime`、`StepWrites.keepOK`、`keep_step`、`ScreenPage`（`step_at`、`op_91`、`cyc_91`、`tilesOf`）。
* 循環はない: フレーム `n` の `TilesIn` は、行と `n` より前のフレームと、フレーム `n` の `j` より前の命令から出る。歩きの検査は ROM の上のもの。

## 証明していないこと

* 頭の読みでの `roomRead`: 頭のための読みは空のタイルかコインを返す。`TilesIn` があれば、これは頭のマスのマップの条件になる。頭の上のマスはれんが、ブロック、床、土管ではない。証明には、いくつものフレームにわたって頭がどこにありうるか（天井の高さ、左の壁）が要る。1 つのフレームの歩きはそれを知らない。

## Lean

`Theorems/ReadTiles.lean`: `ReadH`、`ReadIn`、`read_of`、`inBuf`、`keepOKB`、`zero_mem_tilesOf`、`rd16zp_state`、`mIzy_state`、`erase_ram`、`tiles_step`、`frame_of_walkVI`、`frameVI`、`inv_end`。`Theorems/RoomMap.lean`: `TilesIn`、`tileRow`、`startCheckT`（連言を 1 つ追加）、`tiles_of_state`、`tiles_of_invL`、`tiles_of_rows`。`Theorems/EraseRange.lean`: `yI`、`valOf_y`、`go_staZp_a`、`xferY`、`xferY_ok`。`updF` は `xferY` を加え、`rulesOf` は境界を読みの前の `TAY` にも通す。`Theorems/LoopTime.lean`: `readInOK`、`readIn_of_ok`、`tilesChk`、`chk1T`、`chk2T`、`chk4T`（歩きはこれを使う）、`read_of_chk`、`tiles_of_chk`、`zero_tiles`、`tilesI_of`。`RestU` と `RestB` は `read` の代わりに `readH` を求める。`rec_frame1B` から `rec_frame4B` はフレームの始めの `TilesIn` をとり、各命令でそれを返す。`loop_sites_of_rows` は `ReadH` を求める。`Theorems/Route.lean`: フィールド `roomRead`。

## 再現

```
.lake/build/bin/smbrta buffer-ctl-check FM2 2 tilecheck      # ReadTiles の検査つきの 4 つの歩き、そのあと recCheckB と startCheckT をネイティブで
.lake/build/bin/smbrta buffer-ctl-check FM2 13 tilecheck     # 歩き (iii) だけ（11、12、14: 歩き (i)、(ii)、(iv)）
```
