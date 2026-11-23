[← Back](README-ja.md) | [English](f-5-PoleJoin.md) | [Japanese](f-5-PoleJoin-ja.md)

# 地上: 城に入るのは操作できてから 366 フレームより前にはならない

**主張.** 地上で操作できるフレーム `C` から数えます。`fr j` はフレーム `C + j` です。本物の走りが与えるもの（`Run`。全部のフィールドが仮定で、下に挙げます）から、城に入るのは `C + 366` 以降です。TAS は操作が 852、触るのが `C + 240`（1092）、城が `C + 366`（1218）なので、この下界はちょうどです。

単位は 1/256 ピクセルです。`g` は触ったフレーム、`c` は城に入ったフレームです。`P₂` は移動のあと、当たり判定の前の位置です。`P_s`、`P_f`、`P₀` は、右側が土台の横に届く位置、足が土台の上に入る位置、旗の範囲の左端です。`T = 233`、`N = 126` です。

```
castle_ge     :  Run  →  T + 7 + N ≤ c      (366 ≤ c)
touch_castle  :  Run  →  (T + 1 ≤ g ∧ g + N + 6 ≤ c) ∨ (T + 7 ≤ g ≤ T + 8 ∧ g + N ≤ c) ∨ (T + 9 ≤ g ∧ g + N − 1 ≤ c)
touch_ge   :  Run  →  T + 1 ≤ g             (C + 234 より前には触らない)
```

場合分けです。Lean の中で全部の場合を尽くしています（`direct_castle`、`castle_ge`）。`T'` はジャンプの踏み切りのフレーム、`L` はその前の着地です。

| 触り方 | 証明が与えること | 城 |
|---|---|---|
| 直接つかむのでない | `g ≥ T + 1`（`touch_ge`） | `c ≥ g + N + 6`（`castle_of_other`） |
| 直接、速いジャンプ、着地のあと覚えている速さを書いたフレームがない | どのフレームでも `P₂(g) < P₀`（`fast_near`）。なのでこのつかみ方はない | |
| 直接、速いジャンプ、着地のあと覚えている速さを書いたフレームがある | どのフレームでも `P₂(g) < P₀`（`fast_late`）。なのでこのつかみ方はない | |
| 直接、遅いジャンプ、`g ≤ T + 6` | `P₂(g) < P₀`（`slow_short`）。なのでこのつかみ方はない | |
| 直接、遅いジャンプ、`g = T + 7`, `T + 8` | `v₂(g − 1) < 0` かつ `P₂(g) < P₀ + F`（`slow_tight`） | `c ≥ g + N` |
| 直接、遅いジャンプ、`g ≥ T + 9` | | `c ≥ g + N − 1` |

着地の前は、全部の `k` についてです。`e` は土台の上に入り、そのあと `L` まで足が中にある最後のフレームで、`k = L − e` です（`crossed`、`landing_cases`）。

| | 着地の位置の上限 |
|---|---|
| そのような `e` がない、または `k ≤ 1` | `P'(L) < P_f + 16·v_top − 256` |
| `k = 2` | `P'(L) ≤ P₂(e) − 224`、そして `P₂(e) < P_f + 16·v_top` |
| `k ≥ 3` | `P'(L) ≤ P₂(e) + 256·(k − 2) − 224`、そして `P₂(e) + 16·v_top·(T − e) ≤ B` |
| `L` のあと覚えている速さを書かない速いジャンプ、`k ≥ 2` | 覚えている速さを書くフレームがあると、空中のしきい値より小さくなる。なので書くフレームはなく、毎フレーム押し戻される: `P(L) ≤ P₂(e) − 256`（`fast_pushes`） |

着地のあと（`hop_short`）。`m = g − L − 1` として、`P'(L) − 16·m + 32 < P₀` なら `P₂(g) < P₀` です。各フレームは土台の横にいても、その左にいてもかまいません。

[旗を下からつかむ](f-1-PoleGrab-ja.md) のパラメータは [地上](e-1-SurfaceRun-ja.md) から来ます。

```
t = T,   B = P_A + X + 16·v_top·(T − N),   P₀ = poleP
B + 32 < P₀                                   Statement.gap
P_f ≤ P₂(e),  e + d = T   →   P₂(e) + 16·v_top·d ≤ B      hB_of_line。Statement.after と hit_bound から、ぶつかる場合も含む
```

Lean: `Theorems/PoleJoin.lean`、非公開の `pole_join_numbers`、`pole_falls`、`pole_frac`、`pole_join`、`pole_touch`。`pole_join` は非公開の `surface_run`、`castle_walk`、`jump_grab`、`pole_rules`、`top_frictionCheck`、`pole_falls`、`pole_check_z`、`pole_frac`、`keep_check` を適用しているので、これらは仮定に現れません。操作の始まりの地図と二つのバイト（`hm`、`hw`）を受け取ります。（`keepCases` のチェック `pole_keep` はなくなりました。覚えている速さは機械から読みます: [速いジャンプの前の覚えている速さ](f-6-9-1-StopRead-ja.md)。）

## つないだことで道筋のページから変わること

* **速いジャンプでつかむのは別のことです。** 速いジャンプのフレーム 1 は、遅いジャンプのフレーム 2 より 2 ピクセル低いです。次のフレームで足が土台の中にあり、土台が右を止めるので、終わりの処理はすぐ城に入ります。本物のフレームで位置を書き換えて試すと、城は触った 1 か 2 フレーム後です。[旗に触ってから城まで](f-4-CastleWalk-ja.md) は遅いジャンプしか動かしていません。なので下界には、1092 より前だけでなく、どのフレームでも速いジャンプでつかめないことが要ります。`fast_short` がこれを時刻なしで証明します。TAS の 1085 からの本物の速いジャンプは `P₀` に 912/256 ピクセル足りません。
* **触った + 126 は下界ではありません。** 左に動いていない遅いジャンプで、端数が 176/256 ピクセル以上だと、本物のフレームで位置を書き換えて、触った + 125 です。`g = T + 7` と `T + 8` ではこれは起きません: `slow_tight` により、前のフレームは左に動き、端数は `F = 176/256` ピクセルより小さいです。これには、土台の高さの落下が 3 フレーム以下であることを使います。`g = T + 8` が要るのはタイマーのためです。そこで + 125 なら `E` は 1218 のままでタイマーが 1 回多く減り、和が 1 小さくなるので 1-2 は 1727 になります。もっとあとでつかむ場合は + 125 でも和は減りません。TAS の 1085 の状態から位置を 16/256 から 160/256 ピクセルまで動かし、A、B、左、右の全部の入力で調べましたが、1092 と 1093 の触りで + 125 はありませんでした（`touch-search-at`）。
* **ほかの触り方は 160 フレームより短いことがあります。** 本物の走り（TAS で最後のジャンプの A を長く押す）は 1086 に旗の上の方に触り、1239 に城に入ります。触った + 153 です。道筋のページの 1246 は誤りです。`castle_ge` に要るのは `N + 6 = 132` だけです。
* **速いジャンプは着地の次のフレームとは限りません。** 地面を走って土台の横にぶつかっても、覚えている速さは消えません。次のフレームのジャンプは速いジャンプです。`fast_late` がこれを扱います。着地のあとのフレームで、移動の終わりの速さが 13 以上のものがあればよいです。空中で左右を押さないフレームのあとの速いジャンプは、着地のときの覚えている速さを読みます。これは `fast_near` がどのフレームでも扱います（[着地から速いジャンプまでのフレーム](f-6-9-2-StoredStep-ja.md)）。
* **本物の小さなジャンプは土台の横から離れます。** `PoleGrab.no_grab_far`、`no_grab_near`、`FastHop.fast_hop_short` は、小さなジャンプの全部のフレームが土台の横にいて、`e` から `L` まで足が中にあるとしています。本物の走りはどちらも破ります。たとえば上の速いジャンプは、踏み切りのとき土台の横より 144/256 ピクセル左です。`hop_short` と `crossed` にこの仮定はありません。

## しくみ

`hop_short` は着地のあとの各フレームで状態を追います: 着地の位置から押し戻された、`P_s` より左、そこから押し戻された、のどれかです。`crossed` は `P_f` より左のフレームから追います: 左にいるか、`e` で上に入ってからずっと中にいます。

`fast_pushes` は着地から前へたどります。`e` のあとの各フレームは止まって始まるので、`−12 ≤ v₂ ≤ 2` です。覚えている速さを書くフレームは `|v₂|` を書きます。これは空中のしきい値 `A` より小さいです。着地の終わりの覚えている速さは `A` 以上です。なので各フレームは覚えている速さと動く向きを保ち、動く向きは右のままです。

`approach_of_cases` は踏み切りから着地まで逆にたどります。踏み切りは `A` 以上を読みます（`reads`）。各フレームは覚えている速さに `|v₂|` を書くか、保ちます（`Run.stored_step`）。なので、着地のあとのあるフレームで `|v₂| ≥ A` であるか（`fast_late`）、着地の終わりの覚えている速さが `A` 以上です（`fast_near` と `fast_pushes`）。

`line` は本物の走りでの位置の上限です。最初のヒット `h` の前は `Statement.after` です。`h` ではヒットの 2 種類です。そのあとは `hit_bound` で、フレームを `Chain` にします。最初の `N + E` フレームは 1 フレーム `16·v_top` だけを使い、`P_f` にはまったく届きません。第 24 回: フレームは `wide` つきの `TopSpeed.Frame` です（基点 B は位置と画面の左端の大きい方）。だから `line` は `SurfaceRun.hit_boundB` を `seg_chainB` と `Surface` の部分 `base`、`links`、`base₁` とともに使います。最初の `N + E` フレームでは max(P, B) を 1 フレーム `16·v_top` で抑えます（`early_leB`）。数は変わりません。

`side_of_rule`、`inBlock_of_rule`、`md_of_right`、`push_of_rule` は `PoleGrab.ruleOk` から `Side`、`InBlock`、動く向き、押し戻しを読みます。なので `Collides` から `poleCheck` がこれらを与えます。`maskL_of_step` は `maskCheck` で同じことをします。`grab_frame` はジャンプの道筋に `Jump.arc_spec` を使い、`g = T' + 1` または `T' + 2` を読みます。

仮定だった次の 3 つは定理になりました。

```
J ≤ h                       first_of_surface    box, off, SurfaceRun.noHitCheck
FastLink  ∨  ∃ j,  L < j < T',  13 ≤ |v₂(j)|     approach_of_cases, fastLink_of_cases   reads, air, poleCheck, Run.stop_step, Run.stored_step
L ≤ e + 3                   rows_of_cases       fall, air, fallCheck, base_late
```

`fallCheck` は全部の落下の探索です。地面と 1 から `rows` 段上からの全部のジャンプと、2 から `rows` 段上のブロックから降りる全部の落下を、落下の力と持ち越した端数ごとに調べます。足が土台の高さにあるフレームが続く数を数え、3 以下であることを確かめます。120 フレームで全部の落下が終わるので、探索に長さの仮定はありません。1 段のブロックから降りると 4 フレームなので、これは探索に入れません。`base_late` がこれを除きます。フレーム `w − 1` で足が土台の上にあれば、位置の上限から `w ≥ T + 1` です。なので落下はフレーム `T + 1` より後です。

## 位置の端数と城の旗

`seq j` は数えたフレーム `j` の終わりの機械です。走りのフレーム `a + ix(j)` で、`ix(j)` は操作から `j` 番目にポーズでない状態で終わるフレームです。定義です（`Run.seq`）。触る前もあとも、どのフレームでもそうです。`castle(m)` は `StarFlagTaskControl` が 0 でないことです。`frac(P) = P mod 256` は `CastleWalk.atPole` が書くバイトです。`fracs` は 16 の倍数の 16 個と 255 です。

```
keep            :  FrameKeep.Keep: 触るまでの本物の機械のフレーム          （フィールド）
seq j           =  S.seq(a + ix(j))                                           （定義: Run.seq）
fracCheck       :  posP(B.m) mod 16 = 0                                       （pole_frac、native_decide）
keepCheck       :  操作中の 1 フレーム全体の歩き                              （keep_check、native_decide）
AtCtl(seq 0)    :  seq 0 は操作中のフレームの始まりで、城の旗は立っていない   （引数。Route.Run.atCtl₀）
Run.fracP       :  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0),  Run  →  ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac        :  同じもの  →  P₂(g) mod 16 = 0
Run.frac_mem    :  同じもの  →  frac(P₂(g)) ∈ fracs
toCastle        :  c ≤ upTo(top)   （フレーム top の終わりまでに c 個のフレームがポーズでない状態で終わる）   （フィールド）
atCastle        :  castle(seq c) = true                                       （フィールド）
Run.noCastle_of :  同じもの  →  ∀ j ≤ g,  castle(seq j) = false
Run.afterTouch  :  同じもの  →  g < c
```

`Run.fracP` は機械から `P(j) = posP(seq(j − 1))` を読みます。操作できるときに城の旗は立っていません（`AtCtl(seq 0)`）。`posP(seq 0) = posP(B.m)` は 16 の倍数です（`Start.P`、`fracCheck`）。`AtCtl(seq 0)` は横の土管から出る切り替えの段から出ます（[地上で操作できるときの機械](f-6-2-ControlStart-ja.md)）。触るまでの各フレームは両方を保ちます。`keep` のフレームでの、操作中の 1 フレーム全体の歩きです（[操作中の 1 フレーム全体は城の旗と端数の下のビットを保つ](f-6-19-FrameKeep-ja.md)）。`Run.frac` は `P₂ = P + 16·v₂` を足します。ですから `CastleWalk.Statement.anyFraction` が確かめる端数は、走りの端数になりました。`flagAny` と `flagTight` は、確かめた触り方を端数 `frac(P₂(g))` で名指しします。`castle_of_direct` は `frac(P₂(g)) ∈ fracs` を `Run.frac_mem` から受け取ります。`flagAny`、`flagTight`、`other` の旗は `castle(seq ·)` です。別の関数ではありません。

位置の端数はプレイヤーの `SprObject_X_MoveForce` のバイトです。`MoveObjectHorizontally` はこれに速さの下 4 ビットの 16 倍を足します。1 フレーム全体がその下 4 ビットを保つことは、いまは歩きで証明しています。各命令の条件（`FrameKeep.CleanK`）のもとでです。前はコードから読んだフィールド `fracStep` でした。

触るまで城の旗は立たない。`StarFlagTaskControl` が 0 から変わるのは面の終わりの `PlayerEndLevel` だけです。星の旗の物は、それが 0 のあいだ何もしません。同じ歩きが、操作中の 1 フレーム全体は旗を立てないことを証明します。ですから `keep` とチェックがあれば、操作できるときの機械だけで足ります（`Run.noCastle_of`）。前はフィールド `noCastle` でした。`Route` はもう `Run.afterTouch` を使いません。`level_ge_of_parts` は `g < c` をつなぎの上限（`touch_castle`）から読みます。`Run.segsOk`、`Run.hT`、`Run.hc` はそれを引数にとります。

フィールドは次のように変わりました。

* なくなったもの: `flag`（別の関数）、`afterTouch`（定理 `Run.afterTouch` になった）。
* 増えたもの: `fracStep`、`noCastle`。`atCastle` は機械を読みます: `castle(seq c) = true`。`flagAny`、`flagTight` は `P₂(g)` の端数を使います。
* `direct_castle`、`castle_ge`、`touch_castle` の新しい引数: `hc` のあとの `(hfq : fracCheck sy (above m0 n) = true)`。
* そのあと、なくなったもの: `fracStep`。増えたもの: `keep : FrameKeep.Frames sy m0 g seq`。`direct_castle`、`castle_ge`、`touch_castle` の新しい引数: `hfq` のあとの `(hkc : FrameKeep.keepCheckOf sy m0 = true)`。`Run.fracP`、`Run.frac`、`Run.frac_mem` は `hq` のあとに `(hk : FrameKeep.keepCheckOf sy m0 = true)` をとります。
* そのあと、なくなったもの: `noCastle`、`keep` のフィールド `start`。`keep` に増えたもの: `ctl`、`lagStart`。`direct_castle`、`castle_ge`、`touch_castle` の新しい引数: `A` のあとの `(hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))`。`Run.fracP`、`Run.frac`、`Run.frac_mem`、`Run.noCastle_of` は `hk` のあとに `(hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))` をとります。`Run.afterTouch` は `st`、`hq`、`hk`、`hc0` をとります。
* そのあと、`keep` からなくなったもの: `fm`、`pad`（`all` と `ix` から読む `Frames.fm`、`Frames.pad` になった）、`ends`（定理 `Frames.ends` になった）、`lag`、`lagStart`（定理 `Frames.all_start` になった）。`keep` に増えたもの: `all`、`inp`、`next`、`ix`、`ix0`、`order`、`at_ix`。`ctl` と `clean` は、数えるかどうかによらず、触るまでの全部のフレームについて言うようになった。`PoleJoin` の型は変わっていません。
* そのあと、なくなったもの: `fm`、`inp`、`pass`、`pos`。`touches` は `keep` のフレーム `g` について言います（`Touches(keep.fm g, keep.pad g)`）。増えたもの: `tiles`、`edge`、`moved`（[旗に触るフレーム: 1 フレーム全部](f-6-16-PoleFrame-ja.md)）。`keep` の `ctl` は、ルーチンとタスクの 2 バイトだけを仮定します。モードがゲームのものであることは定理 `Frames.ctlAll` です。`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle` の引数 `hc` は `(hc : PoleFrame.poleFrameCheck sy m0 = true)` になりました（前は `PoleEntryRule.ruleCheck`）。`Run.inRange` は `hc` のあと `R`、`st`、`hq`、`hk`、`hc0` をとります。
* そのあと（項目 1-1-0-4）: `Run` は走り全体の本物のフレームと操作のフレームをとります。`Run sy m0 b vs B T J Nc F S a`、`S : FrameKeep.RealRun`、`a : Nat`。`keep : FrameKeep.Frames sy m0 S a g seq` も同じです。`keep` からなくなったもの: `all`、`inp`、`next`（`all n = S.seq (a + n)` は定義、`Frames.next` は定理）。新しい定理 `Run.seq0 : seq 0 = S.seq a`。前のつなぎ `Route.Run.atCtl` はいまは同じ名前の定理です。非公開の `pole_join`、`pole_touch`、`pole_touch_castle` は `S`、`a` を暗黙の引数にとります。
* そのあと、`keep` からなくなったもの: `ctl`（`keepCheckOf` の 2 つ目の歩きからの定理 `Frames.ctlAll` になった）。`keep` に増えたもの: `noStore`（触るフレームの前のフレームのどの命令も、ルーチン、モード、タスクを番地で書かない）。`edge` が変わりました。画面の端の書き込みと頭の当たりのルーチンを禁じません。書き込みまで、そのどちらかのすぐあとでは、旗の範囲より左にいる、というものです（`PoleFrame.again`）。型は変わっていません。
* そのあと、`keep` からなくなったもの: `ix`、`ix0`、`order`（数えるフレームはいまはポーズでない状態で終わるフレームで、定義です: `Frames.ix`。定理 `Frames.ix0`、`Frames.order`、`Frames.up`、`Frames.down`）、`at_ix`（いまはフィールド `seqAt`）、`clean`（そのあとフィールド `cleanF`、`FrameKeep.guardF` の `CleanK`。定理 `Frames.clean`。いまはフィールド `cleanE`、`FrameKeep.guardE` の `CleanK`。定理 `Frames.cleanF`、`Frames.clean`）。`keep` に加えたもの: `top`、`many`（フレーム `top` の終わりまでに `g` 個のフレームがポーズでない状態で終わる）。`frames` のフィールド `unpaused`、`lagPaused`、`spare` はなくなりました（[地上のフレーム](e-2-SurfaceFrames-ja.md)）。型の変わったものはありません。
* そのあと、なくなったもの: `seq`（定義 `Run.seq = keep.seq` になった。どのフレームでも `seq j = S.seq(a + ix(j))`。ですから触ったあとのフレームも走りの本物のフレームです）、`keep` のフィールド `seqAt`（`keep` は `FrameKeep.Keep sy m0 S a g` になった。`seq` を持ちません。`keep.toFrames` は前の `FrameKeep.Frames` で、`seqAt` は定義から成り立ちます）。増えたもの: `toCastle : c ≤ upTo(upAt, keep.top)`。城に入るのは走りの数えるフレームの終わりです。`flagAny`、`flagTight`、`other` は、`c` までのフレームの旗だけを仮定します（`FollowsTouch sy flag g c E n` は `g + k ≤ c` を仮定します）。弱くなりました。`DirectFlag`、`OtherFlag`、`FollowsTouch`、`DirectWay` は `g` のあとに `c` をとります。`frames` は `SurfaceFrames.OnFrames sy m0 B T J g keep.seq fr keep.toFrames` です。定理の型は変わっていません。
* そのあと、増えたもの: `posKeep`。書き込みまで、添え字かポインタを通してピクセルかページに書くのは、移動のルーチンのそれらへの書き込みで添え字が 0 のときだけ（`PoleFrame.PosKeep`）。`edge` は端の書き込みについてだけ言います（`PoleFrame.again` はそのすぐあとの場所だけ）。歩きは頭の当たりのルーチンを、位置を覚えたまま追います。定理の型は変わっていません。
* そのあと、なくなったもの: `moved`（定理 `Run.moved` になった。触るフレームは移動の終わりに多くても 1 回来る: [`SubsOnce`](f-6-18-2-SubsOnce-ja.md)）。`Run.inRange` は `R` のあとに `hN`、`hfr` を、最後に `hg` をとります。`touch_ge` と `direct_castle` は `Run.inRange` にそれらを渡します。`PoleFrame.poleFrameCheck` は `SubsOnce.subsCheck` も含みます。ほかの定理の形は変わりません。
* そのあと、`ApproachCases` からなくなったもの: `stopped`（定理 `Run.stop_step` になった）、`onGround`（新しいフィールドとともに定理 `Run.ground_step` になった）。増えたもの: `ground`。`L + 1` より後の速いジャンプで、フレーム `T' − 1` は地面で始まり（`st(T' − 2) = 0`）、プレイヤーのルーチンはジャンプを読まない（`jump(T' − 1) = false`）。トラックは機械から読みます。`direct` は `u` だけを与え、トラックは `trackOf sy keep.toFrames u` です（`abs j`、`md j`、`st j` は `seq j` の覚えている速さ、進む向き、プレイヤーの状態。`jump j` は数えるフレーム `j` のプレイヤーのルーチンが読むジャンプ）。`Track` のフィールドが 2 つ増えました: `st`、`jump`。なくなったもの: `Imposes`、`abs_of_imposes`、`keepCases`、`keepCheck`、`StopStep`、`stopStep_spec`。`direct_castle`、`castle_ge`、`touch_castle` は `(hk : keepCheck sy m0 = true)` をとらなくなりました。`approach_of_cases` は `hf`、`hk` をとらず、最後に `hstop`、`hground` をとります。`fastLink_of_cases` は `hf`、`hk` をとらず、最後に `hstop` をとります（[速いジャンプの前の覚えている速さ](f-6-9-1-StopRead-ja.md)）。
* そのあと、`ApproachCases` からなくなったもの: `ground`。増えたものはありません。`Track` から `st`、`jump` がなくなりました。`Approach` は `fastLink`、`fastLate` の代わりにフィールド `fastWay` を 1 つ持ちます: 速いジャンプには `FastLink` があるか、`L < j < T'` で `13 ≤ |v₂(j)|` のフレーム `j` があります。`fast_near` は `(hg : L + 2 ≤ g)` と `(hhop : ∀ j, L < j → j < g → Beside Ps (fr j))` をとります。`fast_late` は `{L j g}`、`(hLj : L < j)`、`(hjg : j < g)`、フレーム `j` の `hfast` をとります。`fastLink_of_cases` は `(hT : T = L + 1)` の代わりに `(htake : sy.AirFastSpeed.toNat ≤ tk.abs L)` をとります。`approach_of_cases` の `hstop` は `T = L + 1 →` がなくなり、`hground` の代わりに `(hkeep : fast = true → ∀ j, L < j → j < T → tk.abs j = (fr j).v₂.natAbs ∨ tk.abs j = tk.abs (j − 1))` をとります。`Run.ground_step` はなくなり、`Run.stored_step` が増えました。`direct_castle`、`castle_ge`、`touch_castle` の形は変わりません（[着地から速いジャンプまでのフレーム](f-6-9-2-StoredStep-ja.md)）。
* そのあと、なくなったもの: `tiles`（`PoleTileWalk.no_write_frameP` の中の定理になった: [触るときの旗のタイル](f-6-17-2-PoleTileWalk-ja.md)）。増えたもの: `bufAll`（操作の始まりから触るフレームまでの各フレームの各命令で、添字かポインタでの書き込みは旗のタイルを旗の列にだけ書く。切り替えの段からの定理である操作の始まりの地図 `PoleTileCtl.colMap₀` とあわせて、触るフレームの始まりの地図が出る: 定理 `Run.tilesStart`）、`tilesRead`（書き込みまで、横の判定の読みはブロックバッファの RAM を読み、旗の列の旗のタイルならページは旗のページの一つ前以上）。`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle`、`Run.inRange` の引数 `hc` は `(hc : PoleTileWalk.poleCheckP sy m0 = true)` になりました。ここから `PoleFrame.poleFrameCheck` も出ます（`poleFrameCheck_of_P`）。この 5 つの定理と `Run.tilesStart` は `hc0` のあとに `(hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0))` をとります。
* そのあと、なくなったもの: `tilesRead`（その「RAM にある」「ブロックバッファにある」の部分は、旗の近くの全部の読みで歩きにより証明した: [旗の近くの読みはブロックバッファにある](f-6-17-3-PoleTileRead-ja.md)）。増えたもの: `ySide`（書き込みまで、横の判定の始まりで、高さは当たり判定のルーチン自身の高さの確認の境より小さい。`PoleTileRead.YSide`）、`tilesFar`（書き込みまで、ページが旗のページの二つ以上前のとき、横の判定の読みの直後のバイトは旗のタイルでない。`PoleTileRead.TileFar`）。`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle`、`Run.inRange`、`Run.tilesStart` の引数 `hc` は `(hc : PoleTileRead.poleCheckU sy m0 = true)` になりました。
* そのあと、なくなったもの: `ySide`（触るフレームの歩きはいま高さを守り、当たり判定のルーチン自身の確認から横の判定まで覚えている: [横の判定の高さ](f-6-17-4-PoleTileHeight-ja.md)）。増えたもの: `yKeep`（書き込みまで、当たり判定のルーチンの中では、添え字かポインタを通して高さを書く命令はない。`PoleTileHeight.YKeep`。`posKeep` や `keep.cleanE` と同じ種類の条件）。`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle`、`Run.inRange`、`Run.tilesStart` の引数 `hc` は `(hc : PoleTileHeight.poleCheckH sy m0 = true)` になりました。
* そのあと、なくなったもの: `tilesFar`（触るフレームの歩きはいま、旗から遠いものも含めて横の判定のどの読みも RAM とブロックバッファにあることを知っている。だから地図により、旗から遠くで読んだ旗のタイルは旗の列にある: [旗から遠い読みはブロックバッファにある](f-6-17-5-PoleTileFar-ja.md)）。増えたもの: `tilesCol`（書き込みまで、ページが旗のページより二つ以上前の横の判定の読みの直後で、旗の列での読みなら、読んだバイトは旗のタイルではない。`PoleTileFar.TileCol`。`tilesFar` はこれをどの列でも求めていた）。`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle`、`Run.inRange`、`Run.tilesStart` の引数 `hc` は `(hc : PoleTileFar.poleCheckF sy m0 = true)` になりました。
* そのあと、なくなったもの: `yKeep`（触るフレームの歩きはいま、操作の始まりからフレームが保つ二つのバイトを使って、当たり判定のルーチンの中の添え字かポインタを通したどの書き込みも高さを書かないことを確かめる: [当たり判定のルーチンの中で高さを守る](f-6-17-6-PoleTileKeep-ja.md)）。増えたもの: `keepB`（触るフレームまでのどのフレームでも、添え字かポインタを通した書き込みは、ブロックの物のオフセットもプレイヤーの番号も書かない。`PoleTileKeep.KeepB`）。`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle`、`Run.inRange`、`Run.tilesStart` の引数 `hc` は `(hc : PoleTileKeep.poleCheckZ sy m0 = true)` になり、`hmap` のあとに引数がもう一つ増えました: `(hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0))`、操作の始まりの二つのバイト（`PoleTileCtl.watch₀`）。`Run.tilesStart` は触るフレームの始まりの地図と二つのバイトを与えます。
* そのあと、狭めたもの: `keepB` は、プログラムだけでは決まらない書き込みにだけ `KeepB` を求めます（`PoleKeepFar.KeepR`。絶対番地と添え字を通した書き込みでもとの番地からどの添え字でもどちらのバイトにも届かないもの、ゼロページと `X` を通した書き込みには求めない）。`bufAll` は、`PoleKeepFar.farBuf` で決まらない書き込みにだけ、そして `STA abs,X`、`STA abs,Y`、`STA (zp),Y` には A が旗の二つのタイルのどちらかのときにだけ `BufAt` を求めます（`PoleKeepFar.BufV`）。一つの命令については、新しい条件は古い条件と同じことを言います。決まる書き込みは証明しました（`keepB_of_R`、`bufAt_of_V`）。測った本物のフレームでは、`keepB` がまだ求めるのは 66 か所、`bufAll` は 7 か所です（[`keepB` と `bufAll` がまだ言っている書き込み](f-6-17-7-PoleKeepFar-ja.md)）。定理の形は変わっていません。
* そのあと、書き直したもの（29 回目）: `tilesCol` は `TileCol` のかわりに `PoleTileFar.TileSlot` を求めます（旗のタイルを読まないところでは `TileCol` より多くを求めます）。ページが旗のページの二つ以上前の横の判定の読みのすぐあと、旗の列で、読んだバイトが旗のタイルなら、触るフレームの始まりのエリアの解析の列は旗の列に来ていた。マリオはフレームの始まりの画面の左の端より高々 112 px 左。読みの列は mod 32 でマリオの画素に 16 px より小さい数を足した列。足したもの: `parWrap`（触るフレームより前の各フレームで、`UpdScrollVar` で 32 px のスクロールのカウンタに左の端の動きを足しても 256 より下、`NoWrapP`）。それらのフレームで左の端が 64,896 px より下なのは定理です（`PoleParserRun.edgeLow_run`。触るのが操作から `farN` フレーム以内のときの、パート e の位置と左の端の評価から）。`keep.cleanE` は少しだけ多くを求めます: `FrameKeep.guardE` はエリアの解析の 4 つのバイトも守る。これらで解析の不変式は触るフレームまでのどのフレームの始まりでも成り立ち、`TileCol` は定理です（[ルートのフレームの上のエリアの解析](f-6-17-10-PoleParserRun-ja.md): `PoleParserRun.inv_run`、`tilesCol_run`）。`Run.inRange`、`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle` は `hgN` のあとに `(hT : R.TileColAll)` を取ります。ルートの非公開の証明が `PoleParserRun.tilesCol_route` でそれを与えます。
* そのあと、狭めたもの（30 回目）: `tilesCol` は `TileSlot` の 3 つ目の部分（読みの列は mod 32 でマリオの画素に 16 px より小さい数を足した列）を、マリオのページが旗のページのちょうど 2 つ前のときだけ求めます。3 つ以上前なら、ほかの 2 つの部分から算術で `TileCol` が出ます（`PoleTileFar.tileCol_of_slot`。29 回目の形から新しい形が出る: `tileSlot_of_R`）。`parWrap` はプレイヤーのルーチンに来るフレームにだけ求めます（ほかのフレームは解析のバイトを保つ。`PoleParser.inv_onFrames` もその `hw` をそこでだけ求める）。各フレームの厳しい規則から出ますが、それは証明していません（[`TileSlot` を 1 つのページだけで、厳しい規則のもとのスクロールのカウンタ](f-6-17-11-PoleWrap-ja.md)）。型: `PoleParser.inv_onFrames` の仮定 `hw` とフィールド `parWrap` は、`∀ k` の前に、プレイヤーのルーチンに着いたこと `∀ n₀, pc = PlayerCtrlRoutine → frame = … →` を取ります。ほかの型は変わりません。
* そのあと、置きかえたもの（31 回目）: `parWrap` はなくなりました。`PoleParserEnd` の歩きを画面のバッファの制御バイトで分けて各フレームの厳しい規則を証明し、解析の不変式を `JV` といっしょに運ぶので（`PoleStrict.invJ_onFrames`）、ルートはもう `parWrap` を使いません。新しいフィールドは、触るフレームより前の、プレイヤーのルーチンに来る各フレームで: `ctlU`（各 `UpdScrollVar` で制御バイトが 6 でない）。前のフィールドより弱くはありませんが、1 つの状態についての条件です。スクロールの量が高々 3 であることはパート e からの定理です（`PoleParserRun.amount_run`）。操作の始まりでの `JV` は切り替えの行からの定理です（`PoleStrict.jv₀`）（[各フレームの厳しい規則](f-6-17-12-PoleStrict-ja.md)）。シグネチャ: `PoleParserRun.inv_run` と `tilesCol_run` は `hs` のあとに `hsc`（`ScrollRule.check`）と `htop`（`top ≤ 48`）を、`h0` のあとに `hJ`（操作の始まりでの `JV`）を取ります。`tilesCol_route` は `hs` のあとに `hsc` と `htop` を、`hmC` のあとに `hmJ`（チェック `jvCheckK`）を取ります。
* そのあと、狭めたもの（32 回目）: `ctlU` は、`UpdScrollVar` で解析が遅れているとき（`S + 3·N ≥ 32`、新しい `parNOf` で）だけ、制御バイトが 6 でないことを求めます。解析が遅れていなければ、制御バイトが 6 のフレームも `JV` を保ちます（`PoleLate.jv_weak`、`PoleStrict.step_strict`）（[解析が遅れていないフレームの制御バイト 6](f-6-17-13-PoleLate-ja.md)）。
* そのあと、移して狭めたもの（33 回目）: `tilesCol` の部分 (slot) はなくなりました。触るフレームの歩きが、場所の地図（解析の列が旗の列まで来ているか、ブロックのバッファに旗のタイルがない）からこれを証明します。この地図は操作の始まりで成り立ち、どのフレームも保ちます（`PoleSlot.frames_slot`。解析の列は戻らない: `PoleParserRun.colMono_run`）。代わりに `bufAll` が多く求めます（`PoleSlot.BufVS`）: 旗のタイルをブロックのバッファに書くには、フレームの始まりの解析の列が旗の列まで来ていることも要ります。`tilesCol` のほかの 2 つの部分が要るのは解析の列が旗の列まで来ているところだけなので、`tilesCol` は、いま、旗の列での遠い読みで、それが来ていないことだけを求めます（`PoleSlot.TileSlotC`）。解析の不変式があれば前の部分からこれが出るので（`PoleSlot.tileSlotC_of_N`）、少なく求めます。`Run.TileColAll` は名前を保ち、いまは触るフレームが解析に求めることを持ちます（[エリアの解析の場所は定理になった](f-6-17-14-PoleSlot-ja.md)）。
* そのあと、狭めたもの（33 回目）: フレームは `JV` のかわりにもっと弱い上限 `PoleLag.JY`（`N ≤ 7 ∧ S + 3·N < 157`）を運びます。解析の不変式と厳しい歩きにはこれで足ります。なので `ctlU` は、`UpdScrollVar` で `S + 3·N ≥ 157` のところだけ、制御バイトが 6 でないことを求めます（測ったどの回にもない）（[エリアの解析の遅れは 157 px まで増えてよい](f-6-17-15-PoleLag-ja.md)）。
* そのあと、狭めたもの（34 回目）: 旗のタイルをブロックのバッファに書く書き込みで、`bufAll` は、フレームの始まりの解析の列が旗の列まで来ているか、書き込みがその列の輪の列にあることだけを求めます（`PoleRing.BufVM`、`NoTileM`）。残りは証明です: `BufV` は旗のタイルを旗の列にだけ置くので、そのような書き込みでは解析の列は `≡ colP (mod 32)` です。そして解析の列は、操作の始まりで旗の列の 32 列前より後にあり（行のチェック、`PoleParserRun.low₀`）、戻りません（`PoleRing.noTileC_of_M`、`Run.low`）。33 回目のフィールドより少なく求めます（[解析は列を輪の中の自分の場所に書く](f-6-17-16-PoleRing-ja.md)）。
* そのあと、なくしたもの（35 回目）: `ctlU` はなくなりました。触るフレームより前の各フレーム全体の歩きが、コインのコードを切って画面のバッファの制御バイトを追います。もとは、コインのタイルのないブロックのバッファの地図です。それは操作の始まりで成り立ち（行のチェック、`PoleParserRun.coinMap₀`）、どのフレームも保ちます（`PoleCoin.frames_coin`、`Run.ctl6`）。これらのフレームの各命令の新しいフィールド: `coinBuf`（添え字やポインタを通す書き込みは、ブロックのバッファにコインのタイルを残さない。`bufAll` が旗のタイルに求めるのと同じ）、`readC`（当たり判定のルーチンの読みや、たたいたブロックの上の読みがコインのタイルを見つけるなら、それはブロックのバッファの中）、`ctlKeep`（添え字やポインタを通す書き込みは制御バイトを書かない）。これらは `ctlU` より弱くはありません。`ctlU` は遅れが 157 px 以上のところでだけ求めました（[ブロックのバッファにコインがないので、制御バイトは 6 でない](f-6-17-17-PoleCoin-ja.md)）。
* そのあと、狭めたもの（35 回目）: `bufAll` は 34 回目の部分（`NoTileM`）を、エリアの解析の列の書き込みでないところでだけ求めます（`PoleRing.BufVR`）。その書き込みでは定理です: 各フレーム全体の歩きがブロックのバッファの列 `B` を解析の列と一緒に追い、書き込みが `B` の輪の列にあること、`B` がどのフレームの始まりでも解析の列の mod 32 であることを示します（`PoleBcol.frames_bcol`、`Run.TileColAll` の新しい部分）。新しいフィールド `bKeep`（添え字やポインタを通す書き込みは `B` を書かない）（[解析は自分の列をブロックのバッファの列に書く](f-6-17-18-PoleBcol-ja.md)）。

本物のフレームで（`pole-frac-check`、最後の変更のあと、exit 0、悪いもの 0）:

| 走り | 回数 | フレーム | 触り | 押し戻しか止まりのフレーム | そのうち左端 |
|---|---|---|---|---|---|
| 動画の、操作から触るまで | 1 | 240 | 1（端数 80） | 5 | 0 |
| 操作できてからの乱数の入力 | 300 | 83,559 | 1 | 4,354 | 3,546 |
| 動画のフレーム 1002 から 1091 からの乱数の入力 | 1,200 | 137,055 | 675 | 6,896 | 732 |
| 画面の左端へ、そのあと乱数 | 720 | 181,894 | 0 | 15,006 | 12,940 |

* 操作できるときの端数は、動画でも証明の機械でも 0 です。
* どのフレームでも `P' − P` は 16 の倍数です。触りには 16 個の端数 `0, 16, …, 240` が全部出て、全部 `fracs` に入ります。
* 触るまで、城の旗のある機械はありません。
* `pole-join-check` は TAS（`frac(P₂(g)) = 80`）、1089 のあと `02808080`（64）、A を長く押した触り（112）で 3 つのフィールドを読みます。旗は、その端数で確かめた触り方の旗と同じです。

触ってから城までの数えるフレームを本物の走りで（`castle-count-check`、exit 0、悪いもの 0）。`g` と `c` は操作から数えたフレームです。フレームはポーズでない状態で終わるとき数えます。

| 走り | 走りの数 | 触る | 城に入る | 触ってから城までのフレーム（ポーズで終わるもの） | `c − g` |
|---|---|---|---|---|---|
| ムービー | 1 | 1 | 1 | 126 (0) | 126 |
| ムービーの触る 2 フレーム前から、フレーム `k`（`k` = 0〜140）と 45 フレームあとに Start | 141 | 141 | 141 | 23,436 (5,670) | 126 |
| 乱数の入力、Start も乱数で、ムービーのフレーム 1052〜1091 から | 200 | 158 | 140 | 41,863 (17,803) | 126、159〜166 |

* どの走りでも、城の旗が最初に立つのはポーズでない状態で終わるフレームです。ですから `c` は数えるフレームで、`seq c` で旗が立ち、`top` をそのフレームにすると `toCastle` が成り立ちます。
* 触ったあと、`c` までの数えるフレームの城の旗は、触ったフレームの終わりから入力なし、ポーズなしで進めた走りのものと同じです。`c − g` も同じです。触ったあとのポーズは、`FollowsTouch` が読むものを変えません。
* 触ってから城まで、フレームを数えるのは時計の位相が動くときとちょうど同じです（`CastleToLevel.kindOf`）。食い違うフレームは 0 です。Lean はまだこれを使いません。`c` は時計の城に入るフレーム `E` とつながっていません（パート 0）。

## 前提（Lean では証明していない）

仮定は `Run` とその中の構造のフィールドです。`pole_join` はこれらを全部仮定します。

| 仮定 | 内容 | 根拠 |
|---|---|---|
| `fr`、`frames.reads` | フレームは機械から読む（`seq` は定義）。`g` では `P₂` までのフィールドだけが本物（触ると動かされる）。`next` は定理 | [地上: 操作できてからのフレームを 1 つずつ](e-2-SurfaceFrames-ja.md) |
| `frames.step` | Clean な状態からの 1 フレームは `OneFrame`。`model`、`hit`、`stop`、`off` は定理 | 同じページの本物の走り |
| `frames.vert`、`frames.box` | `J` より前のフレームは `vstep` のとおりで、当たり判定は操作のときの機械と同じ。`box` は定理 | 同じページの本物の走り |
| `touches`、`posKeep`、`keepB`、`bKeep`、`bufAll`、`tilesCol`、`coinBuf`、`readC`、`ctlKeep`、`edge` | `keep` のフレーム `g` は本物の機械で触る。書き込みまで、添え字を通して位置に書くのは移動のルーチンの添え字 0 の書き込みだけ（`PosAt`）。触るフレームまでのフレームでは、添え字かポインタを通した書き込みはブロックの物のオフセットもプレイヤーの番号も書かない（`KeepB`）。だから操作の始まりのそれらの値（`hwb`、切り替えの段から）で触るフレームはそれらを持って始まり、当たり判定のルーチンの中では添え字かポインタを通して高さを書かないことを歩きが示す（`YAt`、定理）。操作の始まりで、ブロックバッファの旗のタイルは旗の列にある（`ColMap`、引数 `hmap`、切り替えの段から）。触るフレームまでのフレームで、添字かポインタでの書き込みは旗のタイルをそこにだけ書く（`BufAt`）。だから触るフレームの始まりでも地図が成り立つ（`Run.tilesStart`）。これらで、どの横の判定でも、高さが当たり判定のルーチンの確認の境を行に切り上げた 208 px より小さいことを歩きが知っている（歩きがその確認から覚えている）。だからどの横の読みも RAM とブロックバッファにある（歩き）。ページが旗のページの二つ以上前なら、旗の列での横の読みは旗のタイルを読まない（`TileCol`。29 回目から、新しい `tilesCol` である `TileSlot`（33 回目: 歩きが `bufAll` の保つ場所の地図から部分 (slot) を証明し、フィールドは、旗の列での遠い読みで、触るフレームの解析の列が旗の列まで来ていないことだけを求める）とエリアの解析の不変式からの定理: 解析の列は左の端より高々 384 px 先。それには `ctlU`（31 回目、`parWrap` のかわり。32 回目: 解析が遅れているときだけ。33 回目: `S + 3·N ≥ 157` のときだけ。35 回目: `ctlU` はなくなり、`UpdScrollVar` で制御バイトが 6 でないことはコインの地図からの定理 `Run.ctl6`。`coinBuf`、`readC`、`ctlKeep` を使う）と `guardE` の中の解析のバイトが要る）。だから旗のタイルを読んだ横の判定は旗の列を読んでいる（`TileRead`、定理）。画面の端の書き込みのすぐあとで旗の範囲にいるなら、移動の終わりでもいた。`P₂(g)` が移動の終わりの位置であることは定理 `Run.moved`（`SubsOnce`）。`P₀ ≤ P₂(g)` はこれらと `keep` からの定理 `Run.inRange`（1 フレーム全部の歩き） | [旗に触るフレーム: 1 フレーム全部](f-6-16-PoleFrame-ja.md)、[旗のタイル](f-6-17-2-PoleTileWalk-ja.md)、[旗の近くの読み](f-6-17-3-PoleTileRead-ja.md)、[横の判定の高さ](f-6-17-4-PoleTileHeight-ja.md)、[旗から遠い読み](f-6-17-5-PoleTileFar-ja.md)、[当たり判定のルーチンの中で高さを守る](f-6-17-6-PoleTileKeep-ja.md)、[`keepB` と `bufAll` がまだ言っている書き込み](f-6-17-7-PoleKeepFar-ja.md)、[ルートのフレームの上のエリアの解析](f-6-17-10-PoleParserRun-ja.md)、[ブロックのバッファにコインがない](f-6-17-17-PoleCoin-ja.md)、[解析の書き込みはブロックのバッファの列に](f-6-17-18-PoleBcol-ja.md) |
| `keep` | 触るまでの本物の機械のフレーム（数えるかどうかによらない）。操作できるときから続く。走りのフレーム `a` からのフレーム（`all n = S.seq (a + n)` は定義、`next` は定理）。フレームはポーズでない状態で終わるとき数え、数えるフレーム `j` は `seq j = S.seq(a + ix(j))` で終わる。これは定義（`top`、`many`: フレーム `top` の終わりまでに `g` 個のフレームがポーズでない状態で終わる）。触るフレームの前のフレームのどの命令も、ルーチン、モード、タスクを番地で書かない（`noStore`。それらのフレームが操作中に終わることは定理 `Frames.ctlAll`）。各命令は `guardE` の `CleanK` を満たす。これはポーズのバイト、エリアの種類、泳ぎのフラグ、大きさの変化、A と B、前のフレームの A と B、動く向き、走りの速さ、覚えている速さも守る（`cleanE`、[触るまでのフレームの各命令](f-6-21-GuardE-ja.md)）。各フレームが操作中に始まること、`lag` のフレームが城の旗と端数の下 4 ビットを保つことは定理 `Frames.all_start`、`Frames.start`。`16 ∣ P₂(g)` は定理 `Run.frac`、触るまで城の旗が立たないことは定理 `Run.noCastle_of` | [操作中の 1 フレーム全体は城の旗と端数の下のビットを保つ](f-6-19-FrameKeep-ja.md) |
| `toCastle`、`atCastle` | 城に入る `c` は走りの数えるフレーム（`c ≤ upTo(top)`）で、その終わりの機械で城の旗が立っている。`g < c` は定理 `Run.afterTouch`。上限の証明は `toCastle` を使わない。`toCastle` は `c` を本物のフレームまでの数にする。時計とつなぐためのもの | コード。下の `castle-count-check` |
| `other` | 直接つかむのでないとき: 131 フレームのあいだ、`c` まで、数えるフレームの旗は確かめたほかの高さの触り方と同じ | 測定: 触った + 153 以上 |
| `path`、`atY`、`atRising` | ジャンプのフレームは地面からの `Jump.arcSucc` の道筋 | `Jump-ja.md`。地面からのジャンプであること: 旗の近くに踏める敵はいない |
| `order`、`left`、`air` | 左から来て、フレーム `q` から土台の上面より下を落ちる。落下は着地の幅を飛び越せない。足が土台の上にあるフレームでは、ケースの動く向き、高さ、落下の速さはそのフレームのもの | コード。旗の上を越えて戻る走りは含まない |
| `Collides`、`lowCase`、`inBlockCase` | 土台のところのフレームは `cases` の 1 つについて `PoleGrab.collide` のとおり | ルーチンを単独で確認。小さいマリオ |
| `mask` | 右へ押されたあとの速さは、左を止めた `hstep` のとおり。1 フレームのつながり。`maskCheck` は証明済み | 下の本物の走り |
| `reads` | 速いジャンプ: 踏み切りの前の覚えている速さは空中のしきい値以上。モデルのジャンプの種類と機械を結ぶただ 1 つのもの。その前のフレームにフィールドは要らない: 各フレームは覚えている速さに `\|v₂\|` を書くか保つ（定理 `Run.stop_step`、`Run.stored_step`。前のフィールド `stopped`、`onGround`、`ground`） | コード。`Jump.vstep` がこれを読む。`stop-read-check`: ムービーと自分の 233 回の走りで、しきい値以上の覚えている速さを読む踏み切り 76 回（[着地から速いジャンプまでのフレーム](f-6-9-2-StoredStep-ja.md)） |
| `fall` | 遅いジャンプ: 落下は `w ≤ q` で `fallStarts` の 1 つか、土台から降りて始まる。フレームは `fallNext` のとおり | 下のマップの事実 |
| `flagAny`、`flagTight` | 遅いジャンプでつかむと、124 フレームのあいだ、`c` まで、数えるフレームの旗は `P₂(g)` の端数で確かめた直接つかみと同じ。前のフレームが左に動き、端数が `F` より小さければ 125 フレーム | 下の測定 |

操作できるときの状態 `Start` と、操作できるときの機械 `AtCtl` は定理の引数です。`Route.Run.start` と `Route.Run.atCtl₀` が切り替えの最後の段から与えます。

`fall` の中のマップの事実です。非公開の証明では `rows = 8` です。

* 旗の近くで立てるのは、地面と 8 段上までのブロックです。
* 上のブロックは落下を変えません。頭をぶつけると `fallNext` の 1 歩になりません。
* 旗の近くで降りられる 1 段のブロックは土台だけです。なので `fall` は、その前のフレームで足が土台の上にあったと言います。
* 降りるときの落下の力は `Jump.forces` の 1 つです。ジャンプが残した力です。

測定したもの（Lean ではない）:

* 遅いジャンプでつかんだあとの長さ。TAS の直前の状態を書き換えて、高い端数で、速さ、動く向き、覚えている速さ、走りの速さ、走りのタイマーの 2592 通りで、最小は 125 です。触る前に左に動いた 1728 通りでは、端数が 176/256 ピクセルより小さければ 126 以上です。
* ほかの触り方。TAS の状態で高さを 161 通り全部変えて、153 から 164 です。

`Run` は本物の走りで成り立ちます。プログラムで確かめました（`pole-join-check`）。TAS は `h = 234`、`q = 233`、`L = 237`、`T' = 238`、`g = 240`、`c = 366` です。TAS の 1089 のあと左、A、A、A の走りは `g = 241`、`c = 367` です。TAS で A を長く押した走りは、ほかの触り方で `g = 234`、`c = 387` です。作業用のファイルで、TAS の数の `Approach` を Lean の項として作り、`slow_tight` の結論が出ることも確かめました。これはこのフィールドを変える前のことです。

新しいフィールドは、作業用のプログラムでほかの走りも調べました。操作できてからランダムな入力の 500 回で、フレーム 1 から 8 の `box` が成り立ちます。フレーム 1002 から 1089 のあとランダムな入力の 1500 回で、全部の `off` が成り立ちます。着地が 3384 回あり、ジャンプのあとが 3074 回、降りたあとが 310 回です。全部で `fall` が成り立ちます。土台の近くの 1392 回で前のフィールド `stopped` と `onGround` が成り立ちました。そのうち 14 回は速いジャンプの前です。位置を土台の上に書き換えて左を押すと、土台の高さに 4 フレームいて、`fall` の土台から降りる場合が成り立ちます。

`hstep` は覚えている速さを `|v|` にします。`X_Physics` はこれを読みます。ヒットのあと、覚えている速さは `|v|` ではありません。上のランダムな走りで、`hstep` の `v₂` が本物のフレームと違うのは 126510 フレームのうち 59 フレームです。たとえば TAS の 1066 のあと `0082828282c102c1c1...` では、フレーム 1088 で `v = 0`、覚えている速さ 35、左で `v₂ = −1` ですが、`hstep` は 0 です。`Surface.model` は最初のヒットの前のフレームだけのことです。`mask` はこれらの走り全部で成り立ちました。`pole-join-check` は本物の覚えている速さで `v₂` を読むようにしました。

証明していないこと: すべての走りが `Run` を満たすこと。位置の上限 `B` はマップのないモデルのものなので、`fall` が要ります。これがないと `g = T + 7` で `e = T`、`k = 4` を、`g = T + 8` で `e = T + 1`、`k = 4` を除けません。[道筋のページ](../docs/route-1-1-ja.md) のエミュレータの探索はもっと小さな本物の上限を与え、それならこの場合を除けます。`box`、`fall` はフレームのすることを述べています。本物の走りの全部のフレームがそうすることは証明していません。

**ファイル.** `Theorems/PoleJoin.lean`、非公開の `Proof/PoleJoin.lean`。

**再現.**
```
.lake/build/bin/smbrta pole-join-check FM2                  # ムービーのフレームで Run の全部のフィールド（2 秒）
.lake/build/bin/smbrta pole-join-check FM2 1036 HEX         # フレーム 1036 からの入力を入れ替えて同じことを
.lake/build/bin/smbrta pole-frac-check FM2 300               # 本物の走りで 16 ∣ P' − P、fracCheck、城の旗（約 4 分）
.lake/build/bin/smbrta keep-frames-check FM2 100            # 本物の走りで keep の条件
.lake/build/bin/smbrta castle-count-check FM2 200           # 触ってから城までの数えるフレーム、ポーズあり（約 1 分）
.lake/build/bin/smbrta stop-read-check FM2 100              # 本物のフレームで Run.stored_step、Run.stop_step、速い踏み切りの 2 つの場合（約 30 秒）
```
