[← Back](README-ja.md) | [English](0-5-2-1-CastleJoin.md) | [Japanese](0-5-2-1-CastleJoin-ja.md)

# 地上で: 時計の `lag` フレームと、ポーズで終わるフレーム

**主張.** 地上で、操作（`b₂`）から城に入るとき `E` までの各フレームが、ポーズで終わるときにちょうど `clock` の `lag` フレームだとします（`LagUp`、1 フレームごとの条件）。すると `clock` と `pole` は同じフレームを数えます。

* `pole` の数えるフレーム `j` は、`clock` で数が `Cs + j` のフレームです。`j < g` なら遊びのフレーム、`g ≤ j ≤ c` なら `auto` のフレームです。
* `clock` の城に入るとき `E` は、`pole` の数えるフレーム `c` です。フレーム `E` のあとの機械は `pole.seq c` です。
* 地上の `lag` フレームは、ポーズで終わるフレームです。その数は `E + 1 − b₂ − c` です。
* `pole.atCastle` の城の旗は `flag` から出ます。

`LagUp` は `Route.Run` のフィールドではありません。定理が引数として取ります。`route_1_1` は変わりません。

`LagUp` は、地上の各フレームで `clock` の位相が機械の位相であること（`PhaseUp`）と、各フレームでの機械の位相の規則から出ます（`Run.lagUp_of`）。その規則は、触るフレームまでのフレームで証明しました（[操作中の 1 フレーム](0-5-2-1-1-PhaseFrame-ja.md)）。

## なぜ

`pole` は、ポーズでなく終わるフレームを数えます（`FrameKeep.Keep`）。数えるフレーム `j` は `pole.seq j = seq (b₂ + ix j)` で終わります。`ix j` は、`b₂` から数えて `j` 番目の、ポーズでなく終わるフレームです。`clock` は `lag` でないフレームを数えます（`seen`）。地上では 2 つは 1 つの数でしか会いません。`clock` は `E` の前に `Cs + c` フレームを数え（`Segs.last`）、`c` は `pole` の数です。どのフレームが `lag` かは自由です。なので今まで、`clock` の城に入るとき `E`（`flag` が機械を読むところ）が、`pole` の城に入るとき（`atCastle` が城の旗を読むところ）と同じだとは言えませんでした。`LagUp` は 2 つの数え方をフレームごとにつなぎます。

## 定理

`seq` は `base.seq`、`kind` は `clock.kind` です。`r(n)` は `n` より前の、`lag` でないフレームの数です（`seen`）。

```
LagUp        :=  ∀ n,  b₂ ≤ n ≤ E   ⟹   ( kind(n) = lag   ⟺   seq(n + 1) はポーズで終わる )

up(k)        :=  seq(b₂ + k) はポーズでなく終わる                  (FrameKeep.upAt)
U(d)         :=  #{ k ∈ [1, d] : up(k) }                          (FrameKeep.upTo)
ix(j)        :=  j ≤ U(k) となる最小の k ≤ top                     (FrameKeep.ixOf;  pole.seq j = seq(b₂ + ix(j)))

seen_up          :  LagUp   ⟹   ∀ d,  b₂ + d ≤ E + 1   ⟹   r(b₂ + d) = r(b₂) + U(d)
up_E             :  LagUp,  g < c   ⟹   b₂ ≤ E  ∧  U(E + 1 − b₂) = c  ∧  up(E + 1 − b₂)
castle_join      :  LagUp,  g < c   ⟹   seq(E + 1) = pole.seq(c)  ∧  ix(c) = E + 1 − b₂
count_up         :  LagUp,  g < c   ⟹   ∀ j ∈ [1, c],  ∃ n ∈ [b₂, E],  seq(n + 1) = pole.seq(j)  ∧  kind(n) ≠ lag  ∧  r(n) = Cs + j
kind_up          :  LagUp,  g < c   ⟹   ∀ j ∈ [1, c],  ∃ n ∈ [b₂, E],  seq(n + 1) = pole.seq(j)  ∧  kind(n) = (j < g なら play、g ≤ j なら auto)
j_up             :  LagUp,  g < c   ⟹   j = #{ i < b₂ : kind(i) = lag } + (E + 1 − b₂ − c)
atCastle_of_flag :  LagUp,  g < c,  fc.sy = sy   ⟹   castle(pole.seq(c))
```

どれも `Theorems/Route.lean` の `Route.Run.*` です。`g < c` は `Run.hT`、`Run.hc` と同じ仮定です。

証明です。

* `r(b₂) = Cs + 1`（`chg.hb₂`）、`r(E) = Cs + c`（`clock.seen_E`）で、`E` は `lag` フレームではありません（`clock.runs_E`）。なので `r(E + 1) = Cs + c + 1` です。
* `seen_up` は `d` の帰納法です。フレーム `b₂ + d` は、`lag` でないときにちょうど `r` に 1 を足し、ポーズでなく終わるときにちょうど `U` に 1 を足します。`LagUp` はこの 2 つが同じだと言います。
* `b₂ ≤ E` です。そうでないと `r(E + 1) ≤ r(b₂)` から `c ≤ 0` ですが、`c > g ≥ 1` です。なので `U(E + 1 − b₂) = c` で、フレーム `E` はポーズでなく終わります（`E` での `LagUp`）。なので `k < E + 1 − b₂` なら `U(k) ≤ c − 1` です。
* `ix(c)` は `c ≤ U(k)` となる最小の `k ≤ top` で、`c ≤ U(top)` です（`pole.toCastle`）。前の行から `ix(c) = E + 1 − b₂` です（`FrameKeep.nthUp_spec`）。
* `count_up`: `ix(j) ≤ ix(c)`、`U(ix(j)) = j`、`up(ix(j))` です（`FrameKeep.nthUp_at`）。`n = b₂ + ix(j) − 1` とします。
* `kind_up`: `clock.plan` から `kind(n) = Segs.kind(Cs + j)` です。`Cs ≤ Cs + j < Cs + g` なら遊び、`Cs + g ≤ Cs + j` なら `auto` です（`Segs.kind_play₃`、`Segs.kind_after`）。
* `j_up`: `n = E` と `n = b₂` で `r(n) + #lag(n) = n`（`seen_add_lag`）、そして `c ≤ E + 1 − b₂`（`seen_le_add`）です。
* `atCastle_of_flag`: `flag.task_E` は、フレーム `E` のあとで星の旗のタスクのバイトが 2 だと言います。`castle(m)` はこのバイトが 0 でないことです。

## 位相から `LagUp` へ

[操作中の 1 フレーム](0-5-2-1-1-PhaseFrame-ja.md) は、触るフレームまでのフレームで、機械の位相の規則（`PhaseRule`: フレームはポーズで終わるときにちょうど位相 `φ` を保ち、そうでなければ `next(φ) = (φ + 20) % 21` に動かす）を証明します。ここでそれを時計とつなぎます。

```
PhaseAt(n)   :=  clock.ph(n) = phaseOf(seq n)                         (n = 0 では read₀ がこれを言う)
PhaseUp      :=  ∀ n,  b₂ ≤ n ≤ E + 1  ⟹  PhaseAt(n)
PhaseName    :=  タイトルの名前の IntervalTimerControl は PhaseFrame のバイト φ        (ROM でのチェック)

not_setup         :  ∀ n,  b₂ ≤ n ≤ E  ⟹  kind(n) ≠ setup
lag_of_phase      :  PhaseName,  b₂ ≤ n ≤ E,  PhaseAt(n),  PhaseAt(n + 1),  PhaseRule(seq n, seq(n + 1))
                     ⟹  ( kind(n) = lag  ⟺  seq(n + 1) はポーズで終わる )
phase_succ_iff    :  PhaseName,  b₂ ≤ n ≤ E,  PhaseAt(n),  PhaseRule(seq n, seq(n + 1))
                     ⟹  ( PhaseAt(n + 1)  ⟺  ( kind(n) = lag  ⟺  seq(n + 1) はポーズで終わる ) )
lagUp_of_phase    :  PhaseName,  PhaseUp,  ∀ n ∈ [b₂, E],  PhaseRule(seq n, seq(n + 1))   ⟹   LagUp
rule_up           :  チェック,  StartK(seq b₂),  Watched(seq b₂),  tc(seq b₂) = 0,  φ(seq b₂) ≤ 20,  触るフレームまでの KeepsPhase
                     ⟹  ∀ n < ix(g),  PhaseRule(seq(b₂ + n), seq(b₂ + n + 1))
lagUp_of          :  チェック,  StartK(seq b₂),  Watched(seq b₂),  tc(seq b₂) = 0,  PhaseUp,  触るフレームまでの KeepsPhase,
                     hA : ∀ n ∈ [b₂ + ix(g), E],  PhaseRule(seq n, seq(n + 1))   ⟹   LagUp
atCastle_of_phase :  lagUp_of の仮定,  g < c,  fc.sy = sy   ⟹   castle(pole.seq(c))
```

チェックは `FrameKeep.keepCheckOf`、`PhaseFrame.phaseCheck`、`PhaseFrame.tcCheck`、`TitleStart.check` です。`ix(g)` は `b₂` から数えた触るフレームの終わりです。`b₂` での `StartK` と `Watched` は `Run.atCtl₀` と `PoleJoin.Run.watched₀` から出ます。

証明です。

* `not_setup`: `setup` フレームの数は `z₁` か `z₂` で（`Segs.kind`）、どちらも `Cs` より小さいです。地上では数は `Cs + 1` 以上です（`chg.hb₂`）。
* `lag_of_phase`: `clock.step` で、`lag` フレームは時計の位相を保ち、遊びのフレームと `auto` のフレームは位相を `next` に動かします。どの `p` でも `next(p) ≠ p` です。両端で `PhaseAt` なら、時計が位相を保つのはちょうど機械が保つときで、`PhaseRule` は、機械が保つのはちょうどフレームがポーズで終わるときだと言います。
* `phase_succ_iff`: 同じことの逆向きです。
* `lagUp_of`: `PhaseAt(b₂)` と、時計の位相が 21 より小さいこと（`CastleToLevel.Frames.ph_lt`、`ph(0) = 2` から）から `φ(seq b₂) ≤ 20` です。すると `rule_up` が触るフレームまでの `PhaseRule` を、`hA` がそのあとを与え、`lagUp_of_phase` が `LagUp` を与えます。

なので `phase_succ_iff` は、時計の規則が位相をどこまで運ぶかを言います。フレーム `n` が始まるときに時計の位相が機械の位相なら、フレームが終わるときもそうであるのは、ちょうどフレーム `n` が `LagUp` を満たすときです。フレーム 0 の `read₀` から、時計の種類を機械につなぐものがなければ、規則はそれより後のどのフレームも与えません。

## 本物の走りで

`castle-join-check FM2` は、[タイマーと格子](g-1-CastleToLevel-ja.md) のチェックと同じく、`clock` の種類を機械から読みます（`CastleToLevel.kindOf`: 位相が動かないフレームが `lag` フレーム）。フレーム `b₂` が始まるときの機械から走らせ、城に入るときで止めます。

| 走り | 走りの数 | 城に入った数 | `b₂` から城に入るときまでのフレーム | そのうちポーズで終わるもの | `LagUp` の失敗 | `castle_join` の失敗 | `kind_up` の失敗 | `j_up` の失敗 |
|---|---|---|---|---|---|---|---|---|
| 動画 | 1 | 1 | 366 | 0 | 0 | 0 | 0 | 0 |
| `b₂` から城まで 1 フレームおきに、45、50、61 フレームのポーズ | 552 | 552 | 230,580 | 28,548 | 0 | 0 | 0 | 0 |
| 70 フレーム離れた 2 つのポーズ | 74 | 74 | 33,308 | 6,224 | 0 | 0 | 0 | 0 |
| 動画のフレーム `b₂` から `b₂ + 199` のどれかから、ランダムな入力、ランダムな Start | 100 | 19 | 12,290 | 2,622 | 0 | 0 | 0 | 0 |

動画: フレーム 0 は電源を入れてから動画のフレーム 193 です。`b₂ = 853`、`Cs = 852`（`b₂` の前に `lag` フレームはなく、`setup` フレームは 418 と 732）、`E = 1218`、`c = 366`、`g = 240`、`j = 0` です。なので `E + 1 − b₂ = 366 = c`、`Cs + c = 1218 = E` です。城に入るランダムな走りでは `c − g` は 159 から 165（ほかの触れ方）で、ポーズで終わるフレームは最大 322 です。

城に入らない 81 のランダムな走りでは、プレイヤーが操作中のあいだ、位相とポーズはすべてのフレームで合います。操作から離れたあと（死んだあと）の 4,650 フレームで合いません。そのうち 4,643 フレームでは、フレームが始まるときにゲームのタイマーの親の制御（`TimerControl`）が 0 でなく、ポーズなしでタイマーを止めます。ゲームはこれを、死んだとき、ダメージを受けたとき、大きさが変わるときに設定します。どれも `Route.Run` の走りにはありません。

## 証明していないこと

* `LagUp` そのもの。`PhaseUp`、`b₂` での `tc = 0` と操作中の始まり、触るフレームまでの各命令の `KeepsPhase`、`hA` から出ます（`Run.lagUp_of`）。触るフレームまでの機械の部分は証明しました（[操作中の 1 フレーム](0-5-2-1-1-PhaseFrame-ja.md)）。
* `PhaseUp`: 地上の各フレームで `clock` の位相が機械の位相であること。フレーム 0 では `read₀`、`E` のあとでは `flag` がこれを言います。フィールドからは出ません。地上の `clock` の種類は走りとともに選ぶもので、`lag_of_phase` と `phase_succ_iff` は、フレームごとに `PhaseUp` と `LagUp` が同じことを言うと示します。動画で種類を機械から読むと、1,219 フレームすべてで `PhaseUp` が成り立ちます。
* `hA`: 触るフレームのあと `E` までのフレームが `PhaseRule` に従うこと。それらのフレームを追う歩きはありません。城までの 388 の走り（70,995 フレーム）で測りました。
* `pole.atCastle` はフィールドのままです。`PhaseUp` と `hA` をフィールドにすれば定理になります（`atCastle_of_phase`）が、それらは 1 つの機械の条件のかわりに地上の全フレームの条件です。
* 地下と最初の土管の前では、種類は前と同じつながりだけです。`paused₁`、`paused₂`（切り替えの `lag` フレームはポーズで終わる）、数 `ha₁`、`hb₁`、`ha₂`、`hb₂`、フレーム 0 での `read₀` です。

**ファイル.** `Theorems/Route.lean`（`Run.LagUp`、`Run.seen_up`、`Run.up_E`、`Run.castle_join`、`Run.count_up`、`Run.kind_up`、`Run.j_up`、`Run.atCastle_of_flag`。`Run.PhaseAt`、`Run.PhaseUp`、`PhaseName`、`Run.not_setup`、`Run.lag_of_phase`、`Run.phase_succ_iff`、`Run.lagUp_of_phase`、`Run.rule_up`、`Run.lagUp_of`、`Run.atCastle_of_phase`）、`Theorems/CastleToLevel.lean`（`Frames.ph_lt`）。

**再現.**
```
.lake/build/bin/smbrta castle-join-check FM2      # 上の走り（約 140 秒）
.lake/build/bin/smbrta phase-frames-check FM2     # 本物の走りでの lagUp_of の条件（約 115 秒）
```
