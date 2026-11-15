[← Back](README-ja.md) | [English](c-7-5-6-RoomJump.md) | [Japanese](c-7-5-6-RoomJump-ja.md)

# 部屋の落下中に立ってから跳ぶフレーム

**主張.** 地下の部屋で、立っていて A を新しく押した状態でプレイヤーのルーチンに来るフレームは、その高さと、そのフレームが読む覚えている速さとで決まる跳ぶ状態で終わります。なので最初に立ったところから先は、どんな入力でも縦の状態は有限の集まりです。最初に立つのがフレーム `C + 15` 以降なら、この集まりのどの状態も `C + 34` より前に床にいません。それで [地下の部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `fall_jump` は定理になります（項目 1-1-c-7-5）。証明はフィールド `stand_wall` と `wall` を使います。この 2 つはまだ仮定です。床でないところに最初に立つのがフレーム `C + 15` 以降であることを、この 2 つが与えます。この 2 つがないと、縦のバイトだけではこの主張は成り立ちません（下に測った結果）。

記号は [部屋で立って始まるフレーム](c-7-5-5-RoomStand-ja.md) のものです。`Q` はスクロールの処理、`ab(x)` は覚えている速さ（`Player_XSpeedAbsolute`）、`A(x)` はジョイパッドのビットのビット 7、`A'(x)` は前のフレームの A のビット 7 です。`vstepV` はプレイヤーのルーチンの機械での `vstep` です。`layer(d)` は最初の操作から `d` フレーム後の最初の落下の状態の集まりです（[部屋での最初の落下](c-7-5-4-FirstFall-ja.md)）。

```
flat(y)        =  高さ y に立つ縦の状態。ほかの縦のバイトは 0、前のフレームで A は押されていない
jumpOff(y, s)  =  vstepV(flat(y), A を押す, 覚えている速さ s)
vert_jump      :  AtV(x),  st(x) = 0,  A(x) = 1,  A'(x) = 0
                  →  ∃ k ≤ moveLen:  pc(x_k) = Q,  vs(x_k) = jumpOff(y(x), ab(x)),  st(x_k) = 1,  vy(x_k) < 0
jump_frame     :  RoomCond(M)、SiteOK、AtV(tr(k))、jump(readIn(tr(k))) = true、rt(end) = rt_room   →   vs(end) = jumpOff(y(M), ab(tr(k)))
vjump_of       :  C ≤ n < t₀,  n + 1 < E,  jump(n + 1) = true   →   ∃ s,  vs(n + 1) = jumpOff(y(vs(n)), s)
stand_late     :  C ≤ n,  n + 1 < C + 34,  st(vs(n + 1)) = 0,  ¬OnFloor(vs(n + 1))   →   C + 15 ≤ n + 1          （stand_wall、wall、wall_far から）

anyNext(s)     =  next(s)  ∪  { jumpOff(y(s), v)  |  v = 0, …, 255 }      st(s) = 0 のとき                  （next は RoomStand のページ）
               =  next(s)                                                 ほかのとき
anyOk(s)       =  ¬OnFloor(s)  ∧  (st(s) = 0  →  y(s) & 0F = 0)
lands(L)       =  { land(vstepR(s, a))  |  s ∈ L,  a,  falling(vstepR(s, a)) }
anyCheck       :  空の集まりから 1 フレームずつ d = 0, …, 33:  d で初めて見た状態はどれも anyOk を満たす。
                  その anyNext の状態と、15 ≤ d + 1 なら lands(layer(d)) のうち、まだ見ていないものが d + 1 で初めて見た状態
any_ok         :  15 ≤ d',  q(d') ∈ lands(layer(d' − 1)),  ∀ j ∈ [d', n): q(j + 1) ∈ anyNext(q(j)),  n < 34   →   anyOk(q(n))
any_next       :  C ≤ n,  n + 1 < C + 34,  anyOk(vs(n))   →   vs(n + 1) ∈ anyNext(vs(n))
fall_any       :  C ≤ n < C + 34   →   ¬OnFloor(vs(n))
fall_long_of   :  C ≤ n < C + 34   →   ¬OnFloor(vs(n))          （跳ばないときは fall_nojump。これは 2 つのフィールドを使わない。ほかは fall_any）
```

## フィールド

`RoomRun` からなくしたもの:

* `fall_jump`: `C` 以降のフレームで跳ぶ入力があったあと、`C + 34` より前は床にいない。今は `fall_any` が、どんな入力でも証明します。

`RoomRun` に加えたものはありません。`InRoom` に新しく `jump`（証明、`Route.Run.roomJump`）。`Checks` に新しく `anyin`（確かめ `anyCheck`）。`RoomPair.RoomWalks` に新しく `jump`（確かめ `VertJump.jumpOK`）。

`fall_any` は、仮定のまま残る 2 つのフィールドを使います:

* `stand_wall`: 床でないところに立つのは、`hstep` に従わないフレームの終わりだけ。
* `wall`: `C + 37` より前の `hstep` に従わないフレームは、左の壁に止められている。

`stand_late`: フレーム `n + 1` の終わりに床でないところに立つなら、フレーム `n + 1` は `hstep` に従いません。そういう最初のフレームは左の壁にあります。壁は始まりから 13 フレームでは届かない遠さです（`wall_far` と、左への距離の上限 `left_dist_le`）。なので `C + 15 ≤ n + 1` です。

## 方法

**跳ぶフレーム（`VertJump`）.** 立って始まり A を新しく押すフレームで、動きのルーチンはジャンプを始めます。高さの端数、縦の速さとその端数、2 つの力、ジャンプの起点、状態を、読む前に書きます。なので [縦のモデル](../0-0/0-3-2-FrameModel-ja.md) の 2 つの機械の歩きは、この 6 バイトを本物の機械では知らず、`vstep` の機械では 0 として通ります（`vTagsJ`）。高さと覚えている速さは 2 つの機械で同じです。ルーチンの戻りで、歩きは状態が 1 で縦の速さが負だと知っています（`goalVJ`）。結果 `jumpOff(y, s)` は高さと覚えている速さだけで決まります。この ROM では、1 つの高さに対して、256 通りの覚えている速さから 3 通りの跳ぶ状態が出ます。

**フレーム（`RoomJump`）.** 部屋のフレームの新しい歩きは要りません。プレイヤーのルーチンまでの歩き（`RoomVert.before_R`）がフレームの始まりからの縦のバイトを保ちます。`vert_jump` が `Q` でのバイトを与え、そこではジャンプ中で上がっています。`Q` からの歩き（`RoomVert.after_Q`）がフレームの終わりまで保ちます。

**どんな入力でもの状態（`anyCheck`）.** 跳ばないフレームの確かめに、立っているときの跳ぶ状態を加えたものです。16 個の段ちょうどの高さの跳ぶ状態は 1 回だけ計算します（`offTable`: `vstep` を 16 × 256 回）。集まりの中で立つ状態は段ちょうどにいます（`anyOk`）。集まりは空から始まります。フレーム 15 からは各フレームで、最初の落下の層からの着地を加えます。最初に立つ状態は最初の落下の状態からの着地で（`fall_mem`、`fall_next`）、フレーム `C + 15` 以降です（`stand_late`）。`ajRun_sound` は `njRun_sound` と同じ帰納法で、始まりのフレームが自由です。

**縦のバイトだけでは足りない理由.** 部屋のフレームの歩きは、落ちているときどの高さでも着地がありうると言います。ブロックの場所を知らないからです。最初の操作の縦の状態だけから、どのフレームでも着地を許すと:

| 最初に立つのを許すフレーム | フレーム 33 までの状態の数 | 床にいる状態が初めて出るフレーム | プログラムでの時間 |
|---|---|---|---|
| 1 | 55,806 | 31 | 8.4 秒 |
| 2 | 51,703 | 32 | 9.4 秒 |
| 4 | 44,855 | 34 | 11.5 秒 |
| 8 | 22,165 | 34 | 4.8 秒 |
| 12 | 10,487 | 34 | 2.4 秒 |
| 15（`wallF`） | 5,159（高さ 17 から 160） | 34 | 1.6 秒 |

フレーム 1 で立つのを許すと、集まりにはフレーム 31 で床に着く道があります。フレーム 1 で着地し（そこにブロックはありません）、A を押したまま跳んで高さのバイトが画面の上を越えて一周し、床の段より下で着地し、もう一度跳ぶ道です。なので `fall_jump` には、最初に立つのが早すぎないことが要ります。それは左の壁についての事実で、`stand_wall` と `wall` です。

| ROM の確かめ | 大きさ | 時間 |
|---|---|---|
| `jumpOK`（2 つの機械の歩きの 2 つの場合） | | 1 ミリ秒 |
| `anyCheck` | 5,159 状態、跳ぶ状態 4,096 個を計算 | プログラムで 2.4 秒。`Proof/RoomJoin.lean` の中にあります |

## 本物のフレームでの確かめ

プログラム `room-jump-check FM2 [N]`: 確かめ、集まり、そして TAS の部屋での最初の操作から、TAS と、11 種類の自作の入力を `N` 本ずつ（80 フレームまで）。種類 9 と 10 は左の壁へ行き、床でないところに立って始まるフレームごとに A を新しく押します。

| 走り | フレーム | プレイヤーのルーチンで跳ぶ入力のあるフレーム | そのうち `jumpOff(y, ab)` でないもの | 34 より前、床でないところからのジャンプ | 34 より前に床でないところに立つ走り | 最初に立つのが 15 より前の走り | 51 より前のフレーム | そのうち、そのフレームまでに集まりにないもの | 34 より前に床にいる |
|---|---|---|---|---|---|---|---|---|---|
| TAS | 111 | 3 | 0 | 0 | 0 | 0 | 51 | 0 | 0 |
| 自作の入力、11 種類 × 300 | 264,000 | 5,823 | 0 | 49 | 89 | 0 | 168,300 | 0 | 0 |

「そのフレームまでに集まりにある」: 最初に立つまでは、状態はそのフレームの最初の落下の層にあります。最初に立ってからは `anyCheck` の集まりにあり、そのフレームかそれより前に初めて見たものです。5,826 回のジャンプのうち 790 回は、`|v|` でない覚えている速さを読みます。

## 仮定（Lean で証明していないもの）

* `stand_wall`、`wall`（上）: `fall_any` が使います。前からフィールドです。
* `read_stop`、`land_at`（変わらず）。
* 部屋のフレームの各命令での `SiteOK`。[ブロックの地図](c-7-12-RoomMap-ja.md) と同じです。

**ファイル.** `Theorems/VertJump.lean`（`flat`、`jumpOff`、`vTagsJ`、`goalVJ`、`caseOKJ`、`jumpOK`、`vert_jump`）、`Theorems/RoomJump.lean`（`press_of`、`jump_frame`、`jump_room`）、`Theorems/RoomJoin.lean`（`jumpOffR`、`jumpOffs`、`offRow`、`offTable`、`anyNext`、`anyOk`、`fallLands`、`ajRun`、`anyCheck`、`ajRun_sound`、`any_ok`、`InRoom.jump`、`RoomRun.stand_late`、`vjump_of`、`any_next`、`any_chain`、`fall_any`、`fall_long_of`）、`Theorems/RoomPair.lean`（`RoomWalks.jump`）、`Theorems/Route.lean`（`Run.roomJump`、`Run.inRoom`）。非公開の `Proof/RoomVert.lean`（`room_vert_jump`）、`Proof/RoomJoin.lean`（`room_checks.anyin`）。

**再現.**
```
.lake/build/bin/smbrta room-jump-check FM2 [N [K]]    # 確かめ、最初に立つのがフレーム K（15）以降の集まり、本物のフレーム: 11 種類を N 本ずつ（N = 300 で約 2.5 分）
```
