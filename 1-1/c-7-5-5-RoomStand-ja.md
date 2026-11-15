[← Back](README-ja.md) | [English](c-7-5-5-RoomStand.md) | [Japanese](c-7-5-5-RoomStand-ja.md)

# 部屋で立って始まるフレーム

**主張.** 地下の部屋で、立って（状態 0）始まり、A を新しく押さないフレームは跳びません。高さの端数、2 つの力、ジャンプの起点は変わりません。高さ、縦の速さとその端数は変わらず、終わりの状態は 0 か 2 です（立ったまま、または落ち始める）。または着地します。なので最初の操作から跳ばない走りでは、縦の状態は最初の操作の状態からの有限の集まりになります。この集まりの確かめで、[地下の部屋をつなぐ](c-5-RoomJoin-ja.md) の項目 1-1-c-7-5 のフィールド `vfall_stand` と、`fall_stand` の跳ばない部分を証明します。残っていたのはフィールド `fall_jump` です。壁から跳んだあと、`C + 34` より前に床にいないことです。今は項目 1-1-c-7-5-6（[部屋の落下中に立ってから跳ぶフレーム](c-7-5-6-RoomJump-ja.md)）が、フィールド `stand_wall` と `wall` を使って証明します。どのフレームの入力も、今はプレイヤーのルーチンで機械から読みます（モデルに従わないフレームでの新しいフィールド `read_stop`）。それでフィールド `air_in` も証明します。

記号は [部屋での最初の落下](c-7-5-4-FirstFall-ja.md) のものです。`R` はプレイヤーのルーチン、`tr(j)` はフレームの `j` 命令目の機械、`end` はフレームの終わりの機械、`rt` はルーチンのバイトです。`V_S` は高さの端数、2 つの力、ジャンプの起点です。`V_3` は高さ `y`、縦の速さ `vy`、その端数 `mf` です。`A(x)` はジョイパッドのビットのビット 7、`A'(x)` は前のフレームの A のビット 7 です。`jump(n)` はフレーム `n` の入力（`Frames.inp`）のジャンプのビットです。`readIn` は `R` でモデルが読む入力です。

```
StandAt(x)    :  st(x) = 0  ∧  (A(x) = 0  ∨  A'(x) = 1)
StandNext(s, t):  V_S(t) = V_S(s)  ∧  ( (V_3(t) = V_3(s)  ∧  st(t) ∈ {0, 2})  ∨  (st(t) = 0 ∧ vy(t) = 0 ∧ mf(t) = 0 ∧ y(t) = y(s) & F0) )

after_RS      :  RoomCond(M)、各命令で SiteOK
                 →  フレームで pc(tr(j)) = R となる j は多くとも 1 つ、
                    そして  pc(tr(j)) = R,  StandAt(tr(j)),  rt(end) = rt_room  →
                      V_S(end) = V_S(tr(j))  ∧  ( (V_3(end) = V_3(tr(j)) ∧ st(end) ∈ {0, 2})  ∨  (st(end) = 0 ∧ vy(end) = 0 ∧ mf(end) = 0 ∧ y(end) = y(tr(j)) & F0) )
stand_frame   :  RoomCond(M)、SiteOK、pc(tr(k)) = R、st(M) = 0、jump(readIn(tr(k))) = false、rt(end) = rt_room   →   StandNext(vs(M), vs(end))
vstand_of     :  C ≤ n < t₀,  n + 1 < E,  st(vs(n)) = 0,  jump(n + 1) = false   →   StandNext(vs(n), vs(n + 1))
StandNext.vdrop:  StandNext(s, t)  →  VDrop(s, t)

next(s)       =  { s で st := c、A := a  |  c ∈ {0, 2}, a }  ∪  { land(s) で A := a  |  a }                          st(s) = 0 のとき
              =  { vstepR(s, a)  |  a }  ∪  { land(vstepR(s, a))  |  a,  falling(vstepR(s, a)) }                     ほかのとき
ok(s)         =  st(s) = 0  ∨  ( st(s) = 2  ∧  ∀ a,  t = vstepR(s, a):  st(t) = 2,  VDrop(s, t),  falling(t) → VDrop(s, land(t)) )
noJumpCheck   :  vStart から 1 フレームずつ d = 0, …, 49:  d で初めて見た状態はどれも ok を満たし、d < 34 なら床にいない。
                 その次の状態でまだ見ていないものが、d + 1 で初めて見た状態
noJump_ok     :  q(0) ∈ vStart,  ∀ j < n: q(j + 1) ∈ next(q(j)),  n + 1 < 51   →   ok(q(n))  ∧  (n < 34 → ¬OnFloor(q(n)))
nj_next       :  d + 1 < 51,  jump(C + d + 1) = false   →   vs(C + d + 1) ∈ next(vs(C + d))
vfall_of      :  C ≤ n,  n + 1 < C + 51,  st(vs(n)) ≠ 1,  ∀ j ∈ [C, n]: jump(j + 1) = false   →   VDrop(vs(n), vs(n + 1))
fall_nojump   :  C ≤ n < C + 34,  ∀ j ∈ [C, n): jump(j + 1) = false   →   ¬OnFloor(vs(n))
fall_long_of  :  C ≤ n < C + 34   →   ¬OnFloor(vs(n))                                    （fall_nojump。跳んだあとは fall_any、項目 1-1-c-7-5-6）
```

## フィールド

`RoomRun` からなくしたもの:

* `vfall_stand`: 立ったあと、ジャンプの状態でなく跳ばないフレームは `VDrop`。今は `vfall_of` が、最初の操作から跳ばない `vfall` を証明します。
* `fall_stand`: 床でないところに立ったあと、`C + 34` より前は床にいない。今は `fall_nojump` が、最初の操作から跳ばないときに証明します。跳んだときは小さなフィールド `fall_jump` が残ります。

`RoomRun` に新しく加えたもの:

```
fall_jump  :  C ≤ j < n < C + 34,  jump(j + 1) = true   →   ¬OnFloor(vs(n))
read_stop  :  C ≤ n < t₀,  ¬CleanR(フレーム n + 1)   →   inp(n + 1) = readIn(tr(arr(n)))
```

* `fall_jump` は、`n` より前に跳ぶ入力のある走りでの `fall_stand` です。跳ぶ入力は立って始まるフレームにしかありません（`air_in`）。最初に立つところは床ではありません（`fall_first`）。なので `fall_stand` から出ます。
* `read_stop` は、モデルに従わない（横に止められた）フレームの入力が、`R` に初めて来たときに機械から読む入力だと言います。モデルに従うフレームでは `read_in` が入力をそう読みます。`read_inp` が 2 つを合わせます。入力は `Frames` のフィールドです。前は、横に止められたフレームの入力を機械に結ぶものはありませんでした。

`RoomFields` からなくしたもの（今は `RoomCore` のフィールドで、`RoomRun.toCore` が証明します）:

* `air_in`: `C + 51` より前の空中で始まるフレームの入力は空中の入力（状態 1、跳ばない）。`air_in_of`: 入力は機械から読みます（`read_inp`）。`R` でのプレイヤーの状態はフレームの始まりのものです（`InRoom.stR`、`RoomVert.st_at_R` から）。なので 0 でなく、`readIn` は跳びません。機械から読んだ入力はどれも `inputs` にあります（`readIn_mem`）。

変えたもの: `RoomCore.vfall` は、フレーム `C + 1, …, n + 1` で跳ばないことを求めます（前はフレーム `n + 1` で跳ばないこと）。使うのは `drop_run` だけで、そこではこれが成り立ちます。最初の落下と、最初に立ったところから使います。最初に立つまでのフレームは空中で、跳びません（`air_in`）。

`InRoom` に新しく `stand`（証明、`Route.Run.roomStand`）と `stR`（証明、`Route.Run.roomStR`）。`Checks` に新しく `nojump`（確かめ `noJumpCheck`）。`RoomPair.RoomWalks` に新しく `stand`（歩きの確かめ、`RoomStand.SChecks`）。

## 方法

**1 フレーム全体の 4 つ目の歩き（`walkS`）.** [ブロックの地図](c-7-12-RoomMap-ja.md) の歩きを、[RoomVert](c-7-5-1-RoomVert-ja.md) のフレームの形でたどります（`walkV`、`frame_of_walkV`）。`R` で状態を、プレイヤーの状態で分け、状態 0 では `A` と `A'` で分けます。立っていて新しく押さない状態はビットをもらい、リスト `[7, 1]`（`A = 0`）か `[7, 2]`（`A = A' = 1`）になります。`R` でのほかの状態は `[2]` です。そのあと:

| リスト | 意味 |
|---|---|
| `[7, 1]`、`[7, 2]` | `R` で立っていて新しく押さない。`V_S` と `V_3` は書かれていない。状態は書かれてもよい。スクロールのルーチン `Q` でどちらも `[7, 7]` になる |
| `[5, h]` | 同じで、`y` の上の 4 ビットが `h`（着地の `y` との `AND` で分ける） |
| `[1, h, 0]` | そのあと `V_3` が書かれた |
| `[6]` | 着地した: 状態、`vy`、`mf` が 0、`y` が `h` と分かっている。そのあと `y` を忘れる。着地のバイトはそのあと書かれていない |
| `[4, 4, 4]` | リストが許さない段がバイトを書いたかもしれない（ビットを落とす） |

フレームの終わり（`finS`）で、`[4, 4, 4]` か `[1, h, 0]` の状態は部屋のルーチンの外にいなければなりません。`[7, _]` か `[5, h]` の状態は、状態が 0 か 2 と分かっているか、部屋のルーチンの外にいなければなりません。当たり判定のルーチンは、足の確かめの前に状態 2 を書きます。リスト `[7, _]` と `[5, h]` はその書き込みを許します。`after_RS` は、`RoomFall.after_QC` のように、抽象の状態の外の 1 つの事実で歩きを読みます。

最初の試みでは、`R` で両方の片を `[7, 7]` にしました。探索がそれらを合わせたので、ジャンプの確かめで抽象の機械が `A` と `A'` を知らなくなり、ジャンプの始まりが高さの端数を書きました（6 つの終わりが通りませんでした）。`Q` まで 2 つのリストで分けておきます。

**フレーム.** `stand_frame`: `R` までの歩き（`RoomVert.before_R`）が、フレームの始まりから `R` まで縦のバイトを保ちます。そこで `jump(readIn) = false` と状態 0 から `StandAt` が出ます（`nopress_of`）。そこから終わりまで `after_RS` です。`Route.Run.roomStand` が、`Run.roomAir` のように `base` の部屋のフレームで出します（`InRoom.stand`）。

**跳ばないフレーム.** フレーム `n + 1` で跳ばなければ、フレームは `next(vs(n))` の状態に行きます。立っていれば `vstand_of`（`read_inp` からの `jump_read` と）、空中なら `vair_of` です（`nj_next`）。確かめ `njRun` は 1 フレームずつ進みます。フレーム `d` で初めて見た状態は `ok` と床の条件を満たし、その次の状態でまだ見ていないもの（ハッシュの集合）が `d + 1` で初めて見た状態です。各 `vstepR` は 1 回だけ計算します（`njStep`）。`njRun_sound` はフレームについての帰納法で証明します: フレーム `d` までに見た状態は、今初めて見たものか、済んだもの（`ok` と床の条件を満たし、次の状態が集合にある）です。なので `vStart` から `next` をたどる列は、どのフレームでも `ok` を満たします（`noJump_ok`）。最初の形は、すべての状態を最初のフレームとともに並べ、引いて確かめました。各 `vstepR` を 3 回計算したので 15.8 秒でした。

| ROM での確かめ | 状態 | プログラムでの時間 |
|---|---|---|
| `checkS`（`walkS`） | 探索 86,809（表 24,307） | 8.1 秒（探索 4.7 秒） |
| `apartS` | 3 バイトが違う、と `apartC` | 0 秒 |
| `noJumpCheck` | 14,775 状態（状態 2 が 14,087）。フレーム 0, 10, 20, 30, 40, 50 で初めて見たもの: 1, 70, 198, 344, 510, 682 | 2.6 秒 |

`checkS` は数秒より長くかかります。専用の非公開のファイル `Proof/RoomStand.lean` に入れました。

## 本物のフレームでの確かめ

プログラム `room-stand-check FM2 [N]`: 確かめのあと、映像の部屋での最初の操作から、映像と、自分の入力 7 種類それぞれ `N` 回（80 フレームまで。種類 5 と 6 は左の壁へ行く）。フレームのジャンプのビットは、`R` に初めて来たときの `readIn` のものです。

| 走り | フレーム | 立って始まる | そのうち跳ばず部屋で終わる | `StandNext` でない | 落ち始める（終わりで状態 2） | 最初の操作から跳ばないフレーム（51 より前） | そのフレームまでに集合にない | `VDrop` でない | 跳ばずに 34 より前に床にいる | 34 より前に跳ぶ走り | そのうち 34 より前に床にいる |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 映像 | 111 | 6 | 3 | 0 | 0 | 35 | 0 | 0 | 0 | 0 | 0 |
| 自分の入力、7 種類 × 300 | 168,000 | 18,296 | 14,061 | 0 | 49 | 80,817 | 0 | 0 | 0 | 9 | 0 |

どのフレームでも入力を `R` で読むとき（`read_stop`）、入力について言うほかのフィールドも成り立ちます:

| 走り | 34 より前の空中か跳ぶフレーム | そのうち向きが変わった（`facing`） | 51 より前の空中で始まるフレーム | そのうち空中の入力でない（`air_in`） |
|---|---|---|---|---|
| 映像 | 34 | 0 | 50 | 0 |
| 自分の入力、7 種類 × 300 | 71,353 | 0 | 98,232 | 0 |

## 仮定（Lean で証明していないもの）

* `fall_jump`（上）はここでは仮定でした: `C + 34` より前に跳ぶ入力のある走りだけ。項目 1-1-c-7-5-6 から定理です。
* `read_stop`（上）: モデルに従わないフレームでの入力の読み。
* `land_at`（変わらず）: 壁に触らなければ `C + 34` で立つ。
* 部屋のフレームの各命令での `SiteOK`。[ブロックの地図](c-7-12-RoomMap-ja.md) と同じです。

## まだ要るもの

* `fall_jump`: 項目 1-1-c-7-5-6 で済みました。跳ぶ状態は高さと覚えている速さだけで決まり（この ROM では 1 つの高さに 3 通り）、部屋の新しい歩きは要りませんでした。ただし縦のバイトだけでは出ません。最初の操作からの集まりは、フレーム 31 で床に着きます。最初に立つのがフレーム `C + 15` 以降であることが要り、それは `stand_wall` と `wall` から出ます。
* `land_at`: どのフレームで着地するかには、ブロックの地図の上での当たり判定の足の確かめが要ります。

**ファイル.** `Theorems/RoomStand.lean`（`vRestS`、`vLand3`、`StandAt`、`standP0`、`standP1`、`newP`、`piecesS`、`phS`、`outR`、`finS`、`checkS`、`piecesS_class`、`piecesS_cover`、`apartS`、`after_RS`、`nopress_of`、`stand_frame`、`SChecks`、`stand_room`）、`Theorems/RoomJoin.lean`（`StandNext`、`StandNext.vdrop`、`noJumpNext`、`noJumpOk`、`njStep`、`njAdd`、`njRun`、`noJumpCheck`、`njStep_eq`、`njAdd_spec`、`NjDone`、`njRun_sound`、`noJump_ok`、`mem_noJumpNext_air`、`mem_noJumpNext_stand`、`joyOf_mem`、`readIn_mem`、`InRoom.stand`、`InRoom.stR`、`RoomRun.read_inp`、`jump_read`、`air_in_of`、`vstand_of`、`nj_next`、`nj_ok`、`vfall_of`、`fall_nojump`、`fall_long_of`、`drop_run`）、`Theorems/RoomVert.lean`（`st_at_R`）、`Theorems/RoomPair.lean`（`RoomWalks.stand`）、`Theorems/Route.lean`（`Run.roomStand`、`Run.roomStR`、`Run.inRoom`）。非公開の `Proof/RoomStand.lean`（`room_stand`）、`Proof/RoomJoin.lean`（`room_checks.nojump`）。

**再現.**
```
.lake/build/bin/smbrta room-stand-check FM2 [N]    # 確かめ（約 15 秒）と本物のフレーム、7 種類それぞれ N 回（N = 300 で約 1.5 分）
```
