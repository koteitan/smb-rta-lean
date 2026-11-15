[← Back](README-ja.md) | [English](c-7-5-4-FirstFall.md) | [Japanese](c-7-5-4-FirstFall-ja.md)

# 部屋での最初の落下

**主張.** 部屋で最初に操作できるとき、縦の状態は分かっている 1 つの状態です。部屋への切り替えの段がそれを知っています（`InRoom.vstart`）。最初に立つまで、どのフレームも空中で始まります。なので前の状態の `vstepR` か、その着地です（[部屋でのジャンプの各フレーム](c-7-11-1-RoomFall-ja.md)）。着地は立つことです。ですから最初に立つまで、最初の操作から `d` フレームあとの状態は最初の落下の状態です。最初の状態から、A を押すか押さないかで `vstepR` をとったものです。この状態の有限の確かめで、[地下の部屋をつなぐ](c-5-RoomJoin-ja.md) の項目 1-1-c-7-5 の 3 つのフィールド `fall_long`、`vfall`、`floor_at` を、最初に立つまでのフレームで証明します。残るのは、立ったあとのフレームと 1 つの状態のことです。小さな 3 つのフィールドになります。

`vs(n)` は部屋のフレーム `n` の終わりの縦の状態、`C` は最初の操作、`t₀` はかたまりの右端を越えた最初のフレームです。`st` はプレイヤーの状態です（0 立っている、1 ジャンプ、2 落下）。`OnFloor(s)` は `st(s) = 0 ∧ y(s) = y_ground` です。`Y = 256·y + 端数`、`W = 256·vy + 端数`、`f` は落下の力です。`VDrop(s, t)` は `st(t) ≠ 1 ∧ Y(t) ≤ Y(s) + W(s) ∧ W(t) ≤ W(s) + f(s) ∧ f(t) = f(s)` です。`land(t)` は `t` の `y := y & F0`、`vy := 0`、速さの端数 0、`st := 0` です。部屋の数: 落下は `34` フレーム、`standF = 51`。

```
L₀ = vStart,   L_{d+1} = { vstepR(s, a) | s ∈ L_d, a ∈ {押す, 押さない} }

vstart     :  vs(C) ∈ vStart                                                         (RoomPair.rowsCheck、Route.Run.roomV0)
fallCheck  :  0 < 34 < 51,   P₁ + 16·v_top·51 < goalP,
              ∀ d < 51, ∀ s ∈ L_d:  st(s) = 2、どちらの a でも t = vstepR(s, a) として:
                 st(t) = 2,   VDrop(s, t),   falling(t) → VDrop(s, land(t)),
                 d + 1 < 34 → falling(t) → y(land(t)) ≠ y_ground,
                 d + 1 = 34 → falling(t) ∧ y(land(t)) = y_ground
t0_far     :  C + 51 < t₀
fall_mem   :  d < 51,   ∀ j ∈ (C, C + d]: st(vs(j)) ≠ 0   →   vs(C + d) ∈ L_d
fall_next  :  同じ条件   →   vs(C + d + 1) = t  ∨  (falling(t) ∧ vs(C + d + 1) = land(t)),     t = vstepR(vs(C + d), a(C + d + 1))
vfall_first:  C ≤ n,  n + 1 < C + 51,  ∀ j ∈ (C, n]: st(vs(j)) ≠ 0   →   VDrop(vs(n), vs(n + 1))
fall_first :  C ≤ n < C + 34,  ∀ j ∈ (C, n): st(vs(j)) ≠ 0   →   ¬OnFloor(vs(n))
fall_long_of: C ≤ n < C + 34   →   ¬OnFloor(vs(n))                                           （fall_stand と）
vfall_of   :  C ≤ n,  n + 1 < C + 51,  st(vs(n)) ≠ 1,  jump(n + 1) = false   →   VDrop(vs(n), vs(n + 1))   （vfall_stand と）
floor_at_of:  NoWall   →   OnFloor(vs(C + 34))                                               （stand_wall、land_at と）
```

`P₁` は最初の位置の右端、`v_top` は最高速、`goalP` はかたまりの右端です。`t0_far` は、`C + 51` までのフレームが `t₀` より前だと言います。そこでは部屋の歩きがどのフレームについても言います。

## フィールド

`RoomRun` からなくしたもの（今は `RoomCore` のフィールドで、`RoomRun.toCore` が証明します）:

* `fall_long`: `C + 34` より前は床にいない。
* `vfall`: `C + 51` より前で、ジャンプの状態でなく跳ばないフレームは `VDrop`。
* `floor_at`: 壁に触らなければ、`C + 34` で床にいる。

`RoomRun` に新しく加えたもの（どれも、置きかえる前のフィールドから出ます）:

```
fall_stand :  C < i < n < C + 34,  st(vs(i)) = 0,  ¬OnFloor(vs(i))   →   ¬OnFloor(vs(n))
vfall_stand:  C < i ≤ n,  n + 1 < C + 51,  st(vs(i)) = 0,  st(vs(n)) ≠ 1,  jump(n + 1) = false   →   VDrop(vs(n), vs(n + 1))
land_at    :  NoWall   →   st(vs(C + 34)) = 0
```

* `fall_stand` は、床でないところに立ったあと、つまり左の壁に立ったあとの `fall_long` です。
* `vfall_stand` は、最初に立ったところからの `vfall` です。
* `land_at` は、高さを除いた `floor_at` です。`C + 34` での床の高さは最初の落下が出します。そこで立つことは当たり判定の足の確かめで、証明していません。

`InRoom` に新しく `vstart`（証明、`Route.Run.roomV0`）。`Checks` に新しく `first`（確かめ `fallCheck`）。`Nums` に新しく `vStart`（最初の操作での縦の状態）。

## 方法

**始まり.** 部屋への切り替えの段（[`RoomPair.rowsCheck`](c-7-5-2-RoomPair-ja.md)）は、今は操作できるどの状態でも、`vsOf` が読む 9 バイトが分かっていて、状態が `vStart` にあることも求めます（`rowV`、`v_of_rows`）。生成のプログラムは、縦の土管の入口から入力なしで操作できるまで切り替えを走らせて `vStart` を作ります（`Main.lean` の `roomV0Of`）。この確かめは、`rowsCheck` がほかの 2 つの事実のためにもう作った段を読みます。段をもう一度作ることはありません。

**層.** `fallLayer d` は `L_d` の状態を並べます（`fallNext` と `eraseDups`）。確かめ `fallRun` は層を 1 回たどります（`d = 0, …, 50`）。状態 2 ではルーチンは A を読まず、A は前のフレームの A に入るだけです。なのでどの層も状態は 1 つか 2 つです（A を押すか押さないか）。

| フレーム `d` | 高さ | 速さ（1 フレームのピクセル） | メモ |
|---|---|---|---|
| 0 | 48.41 px | 2.34 | 最初の操作 |
| 14 | 95.44 px | 4.00 | 速さの上限がはじめて効く。ここから速さは 4.00、4.16、4.31、4.47、また 4.00 とくり返す |
| 33 | 175.66 px | 4.47 | ここで着地すると床の 1 段上 |
| 34 | 180.13 px | 4.00 | ここで着地すると床の上 |
| 50 | 247.88 px | 4.00 | 最後の層 |

**最初に立つまで.** `fall_mem` は `d` についての帰納法です。フレームは状態 2 で始まるので、`vair_of` が `vstepR` かその着地を出します。着地は `st = 0` で立つことなので、`vstepR` で次の層にあります。`vfall_first` と `fall_first` は、その状態と次のフレームでの確かめを読みます。

**立ったあと.** `fall_long_of` は `n` より前の最初に立つフレーム `j` をとります（`first_of`）。なければ `fall_first` です。あれば、`fall_first` がそれは床でないと言い、`fall_stand` が `n` を出します。`vfall_of` は、`n` かそれより前に立つかどうかで `vfall_first` か `vfall_stand` です。`floor_at_of`: 壁に触らないとき、`C + 34` より前に立てば、それは最初に立つフレームで床ではありません（`fall_first`）。するとその前のフレームは `hstep` に従いません（`stand_wall`）。壁に触らなければ、そのフレームは `hstep` に従います。なのでフレーム `C + 34` は最初の落下の `vstepR` か、その着地です。`land_at` が立っていると言うので着地で、高さは床です。

**`t0_far`.** どのフレームも動くのは最高速までで（`move_top_of`）、始まりは `P₁` 以下です（`start_P`）。確かめは `P₁ + 16·v_top·51 < goalP` を求めます。かたまりの右端は、最高速で 59 フレーム先です。

| ROM での確かめ | 状態 | プログラムでの時間 |
|---|---|---|
| `fallCheck` | 51 層、101 状態 | 0.06 秒 |
| `rowV` つきの `rowsCheck` | 時間の段（操作できる状態 14,224） | 29.5 秒（段は `rowsCheck` のためにもう作っていた） |

## 本物のフレームでの確認

プログラム `room-first-fall-check FM2 [N]`: 2 つの確かめのあと、ムービーの部屋での最初の操作から、ムービーと、自分の入力の 7 種類それぞれ `N` 回（60 フレームまで）を走らせます。種類 5 と 6 は左の壁に行きます。はじめに何フレームか任意の入力、それから B を押して左、ときどき A です。

| 走り | 回数 | `C + 34` より前に立つ（どれも床でない） | そこから `C + 34` より前に跳ぶ | 最初に立つのが `C + 34` | 最初に立ったところからの跳ばないフレーム | 成り立たない |
|---|---|---|---|---|---|---|
| ムービー | 1 | 0 | 0 | 1 | 0 | 0 |
| 自分の入力、7 種類 × 300 回 | 2,100 | 46 | 13 | 2,054 | 7,493 | 0 |

「成り立たない」は次のそれぞれの数です。最初に立つより前で層にないフレーム。最初に立つより前で `VDrop` でないフレーム。`fall_stand`、`vfall_stand`、強い形の `land_at`（壁に触らない、のかわりに `C + 34` より前に立たない。そのとき `C + 34` で床に立つ）。前の 3 つのフィールド。どれも 0 でした。ムービーの最初の操作での縦の状態は `vStart` のものです。いちばん早く立ったのは `C + 18` でした。

## 仮定（Lean で証明していないもの）

* `fall_stand`、`vfall_stand`、`land_at`（上）。壁に立ったあとのフレームと、`C + 34` の 1 つの状態のことだけを言います。
* 部屋のフレームの各命令の `SiteOK`。[ブロックの地図](c-7-12-RoomMap-ja.md) と同じです（`vair_of` を通して）。

## まだ要るもの

* 壁に立ったあとのフレーム: 立った状態で始まるフレームは、部屋のどの歩きもたどっていません。そういう歩き（跳ばずに立った状態で始まるフレームは、高さ、速さ 0、力を保ち、立つか落ちるかで終わる）があれば、立ったあとの状態もまた有限の集まりになり、`vfall_stand` は `vfall_first` と同じように出ます。`fall_stand` には壁からのジャンプも要ります。
* `land_at`: どのフレームで着地するかには、ブロックの地図の上での当たり判定の足の確かめが要ります。[部屋でのジャンプの各フレーム](c-7-11-1-RoomFall-ja.md) と同じです。

**ファイル.** `Theorems/RoomJoin.lean`（`fallNext`、`fallLayer`、`vdropB`、`fallStep`、`fallOk`、`fallRun`、`fallCheck`、`fall_ok`、`fallStep_spec`、`first_of`、`RoomRun.vs_start`、`t0_far`、`fall_mem`、`fall_next`、`vfall_first`、`fall_first`、`fall_long_of`、`vfall_of`、`floor_at_of`）、`Theorems/RoomPair.lean`（`vsBytes`、`rowV`、`rowsCheck`、`of_invL`、`v_of_state`、`v_of_rows`）、`Theorems/Route.lean`（`Run.roomV0`、`Run.inRoom`）。非公開の `Proof/RoomJoin.lean`（`room_checks.first`）、`Proof/RoomVert.lean`（`room_pair_rows`）。

**再現.**
```
.lake/build/bin/smbrta room-first-fall-check FM2 [N]    # 確かめ（約 30 秒）と本物のフレーム。7 種類それぞれ N 回（N = 300 で約 1.7 分）
```
