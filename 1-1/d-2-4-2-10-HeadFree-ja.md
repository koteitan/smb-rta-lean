[← Back](README-ja.md) | [English](d-2-4-2-10-HeadFree.md) | [Japanese](d-2-4-2-10-HeadFree-ja.md)

# 頭の読みを地図の頭のマスから

**主張.** 部屋のすべてのフレームで、頭のためのブロックのバッファのルーチンの読みは、読むマスが地図で空のタイルかコインなら、空のタイルかコインを返す。そこでフィールド `roomRead` は、機械が読むバイトをもう問わない。問うのは頭の読みの場所だけ: そのマスが地図で空いていること (`HeadFree`)。

これは証明した。ROM の検査を 1 つ、すでにある private の証明に足した (`LoopTime.recCheckB` の歩き (i)、`Proof.SiteMusic1`。新しい private のファイルはない)。フィールド `roomRead` を変えた: 読んだバイトのかわりに、読みのアドレスについての条件を求める。足したフィールドはない。

`B` は 2 つのブロックのバッファの 416 バイトの集合、`M` は地図 (`RoomMap.mapRef`: 手本の入りのあと部屋の最初の操作の機械を、入力なしで 91 フレーム進めたもの)、`m(d)` は `m` の RAM のバイト `d`。`T` はタイルのリスト (`P.tiles`、12 個)、`H` は頭のタイル (`P.headTiles`: 空のタイルとコイン)。`read` はルーチンの `LDA (zp),Y`、`addr(m)` はその番地、`val(m)` は読むバイト、`save` はルーチンのオフセットのバイト、`heads` は頭のオフセット。`tr_n(j)` はフレーム `n` の `j` 命令後の機械。`x & y` と `~x` はビットごと。

## 命題

```
ZeroIn(m)     :=  ∀ d ∈ B,  m(d) & ~M(d) = 0                                  (地図で 0 のビットは 0)
HeadFree(m)   :=  pc(m) = read  →  m(save) ∈ heads  →  M(addr(m) & 0x7FF) ∈ H   (頭のマスは地図で空いている)
ReadH(m)      :=  pc(m) = read  →  m(save) ∈ heads  →  val(m) ∈ H                (ラウンド 34 のフィールド)
headSub       :=  ∀ t ∈ T,  ∀ c ∈ H,  t & ~c = 0  →  t ∈ H                      (ROM の検査)

readH_of_free :  headSub,  TilesIn(m),  ZeroIn(m),  ReadIn(m),  HeadFree(m)   →   ReadH(m)
zero_step     :  Sim(A, m),  keepOKB(A),  SiteX(m),  ZeroIn(m)                →   ZeroIn(step(m))
zero_of_rows  :  MapFacts,  startCheckT,  InRowsT(m),  control(m)            →   ZeroIn(m)
```

`TilesIn` と `ReadIn` は [読みでのブロックのバッファのタイル](d-2-4-2-8-ReadTiles-ja.md) のもの: `B` のどのバイトも `T` のタイルで、読みの番地は `B` の中。

`Route.ChangesBase` でフィールドが変わる:

```
前     roomRead : ∀ n ∈ [b₁, a₂),  ∀ j,  ReadH(tr_n(j))
今     roomRead : ∀ n ∈ [b₁, a₂),  ∀ j,  HeadFree(tr_n(j))
```

新しいフィールドだけからは古いものは出ない。部屋の歩きが各命令で証明する `ZeroIn`、`TilesIn`、`ReadIn` があれば出る (`readH_of_free`)。古いフィールドからも新しいものは出ない: ブロックのバッファが、地図でレンガ、ブロック、土管、床であるマスに 0 を持つ機械は、そこで `ZeroIn` と `ReadH` を満たすが `HeadFree` を満たさない。だからそのような状態では、新しいフィールドの方が多くを求める。

## しくみ

**地図のビット.** 部屋のフレームの歩き (`LoopTime.recCheckB`) は、すでにすべての状態で、そのステップが `B` のどのバイトも書かないか、アキュムレータ 0 でのコインの消去であることを確かめている (`ReadTiles.keepOKB`)。そのようなステップは `B` の各バイトをそのままにするか 0 にする (`buf_step`)。0 になったバイトにはビットがない。だから `ZeroIn` はどのステップでも保たれる (`zero_step`)。歩きはこれを `TilesIn` と合わせて 1 つの不変条件 (`LoopTime.MapIn`) として、部屋の最初の操作から、すべてのフレームのすべての命令を通して運ぶ (`ReadTiles.frameVI`)。最初の操作では成り立つ: 部屋への切り替えの行が地図のビットつきの部屋の条件を与え (`RoomMap.start_of_rows`)、手本は地図の外にビットを持たない (`RoomMap.MapFacts.sub`)。

**頭のための読み.** 頭のための読みでは、読むバイトは `B` のバイト (`ReadIn`) で、`T` のタイル (`TilesIn`) で、地図のバイトの外にビットを持たない (`ZeroIn`)。地図のバイトが頭のタイルなら、検査 `headSub` から読むバイトも頭のタイル。この ROM では、空でないリストのタイルで、すべてのビットがコインのビットの中にあるのはコインだけ。

**ROM で.** `headSub` は歩き (i) (`LoopTime.walk1B`) の一部で、`SideRead.xFacts` の隣にある。

## 測ったこと

`buffer-ctl-check FM2 100 headfree` (exit 0、120 秒): 部屋でのムービーのフレームと、そこからの自分の入力 (フレームごとのランダムな入力を 100 回、数フレーム押し続ける入力を 100 回)。それぞれ小さいプレイヤーと大きいプレイヤーで、命令ごとに。

| プレイヤー | 回 | フレーム | 頭の読み | `HeadFree` が偽 | `ReadH` が偽 | `ZeroIn` なしのフレームの始め |
|---|---|---|---|---|---|---|
| 小 | 201 | 65,076 | 65,076 | 0 | 0 | 0 |
| 大 | 201 | 71,395 | 71,395 | 0 | 0 | 0 |

`headSub` は真。頭の読みは 1 つ目のブロックのバッファの 1 から 10 の行にあり、いちばん上の行には一度もなかった (頭の読みでのいちばん小さい高さは 45 px)。これらの走りのすべての頭の読みは、地図で空いているマスだった。

## 証明していないこと

* `HeadFree`: 頭がどこにあるか。地図で空いていないマスは、左の壁、ブロックの上のいちばん上の行のレンガ、ブロック、横の土管、縦の土管、床。頭をそこに入れないには、フレームをまたいで位置を抑える必要がある: 左の壁と土管を壁として、ジャンプの高さをいちばん上の行より下に。部屋のフレームについての部分 c の事実はここでは使えない: それらは `SiteOK` で証明されていて、その頭の条項がこのフィールドだから。

## ほかの部分から使うもの

* 部分 c: `RoomMap.start_of_rows`、`RoomMap.MapFacts` (`sub`)、`RoomMap.startCheckT`、`RoomMap.knownT`、`RoomMap.mapRef`、`RoomMap.TilesIn`、`RoomBlocks.readVal_eq`。
* 部分 d: `ReadTiles` (ラウンド 34)、`LoopTime`、`EraseRange`、`StepWrites.keep_step`。
* 循環はない: フレーム `n` の `ZeroIn` は、最初の操作での行と、`n` より前のフレームとそれより前の命令のステップから来る。
