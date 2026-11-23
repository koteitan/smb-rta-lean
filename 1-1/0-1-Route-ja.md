[← Back](README-ja.md) | [English](0-1-Route.md) | [Japanese](0-1-Route-ja.md)

# 1-1 全体: 1-2 は 1748 より前に始まらない

**命題.** 走りが `Run` の全部の仮定を満たすなら、1-2 が始まるフレーム `L` について `L ≥ 1748 + j` です。`j` は、タイマーが動かないフレームのうち、切り替えの 1 フレームずつを除いた数です。TAS は `j = 0`、`L = 1748` です。

**これは仮定つきの定理です。** `Run` の仮定を全部の走りについて証明してはいません。このページはその仮定の一覧です。

フレームは 1-1 で最初に操作できるフレームを 0 として数えます。`E` はすべてのフレームを数えた番号です。`E_a`、`C_r`、`E_b`、`C_s`、`g`、`c` は `lag` のフレーム（`j` に数えるフレーム）を除いて数えた番号です。

```
P₁ = E_a                 縦の土管に入るフレーム
X₁ = C_r − E_a           地下への切り替え
P₂ = E_b − C_r           地下で操作できてから横の土管まで
X₂ = C_s − E_b           地上への切り替え
P₃ = g                   地上で操作できてから旗に触るまで
W  = c − g               触ってから城まで
E  = C_s + c + j         城に入るフレーム
T                        E でのタイマー
c_E                      E でのインターバルタイマーの位相
```

定理のつながり:

```
P₁ ≥ 368                                                       pipe_no_entry（パート a）
X₁ ≥ 91                                                        Run.change₁（パート b。1 フレームごとの仮定から）
P₂ ≥ 111                                                       room_join（パート c）
X₂ ≥ 282                                                       Run.change₂（パート d。1 フレームごとの仮定から）
(g ≥ 234 ∧ W ≥ 132) ∨ (240 ≤ g ≤ 241 ∧ W ≥ 126) ∨ (g ≥ 242 ∧ W ≥ 125)    pole_touch_castle（パート e、f）
E = P₁ + X₁ + P₂ + X₂ + P₃ + W + j                             Run.hE（clock の規則から）
401 ≤ T + ⌈P₁/24⌉ + ⌈P₂/24⌉ + ⌈P₃/24⌉                          Run.hT（clock の規則から）
─────────────────────────────────────────
E + T ≥ 1588 + j                                               sum_ge
(c_E + E) mod 21 = (3 + j) mod 21                              Run.hc（clock の規則から）
E + T + D + 107 + ((c_E − T − D) mod 21) ≤ L,  D ≥ 33          Run.hD、Run.hL（flag の規則から）
─────────────────────────────────────────
L ≥ 1748 + j                                                   level_ge_of_parts
```

Lean: `Theorems/Route.lean` の `Run`、`Base`、`Changes`、`Run.pipeStart₁`、`Run.pipeKeep₁`、`Run.pipeOne`、`Run.roomCtl`、`Run.roomEnter`、`Run.atCtl`、`Changes.b₁_lt_a₂`、`Run.change₁`、`Run.change₂`、`Run.hE`、`Run.hT`、`Run.hc`、`Run.zero`、`Run.still`、`Run.s_zero`、`Run.ph_zero`、`Run.hD`、`Run.hL`、`Run.start`、`Run.atCtl₀`、`Run.entry₁`、`Run.upStart₁`、`Run.pipeStart₁`、`Run.roomStart`、`Run.inRoom`、`Changes.roomAt`、`RoomChecks`、`level_ge_of_parts`、非公開の `route_1_1`。`#print axioms route_1_1` に `sorryAx` はありません。`native_decide` の分があります。

## 仮定の一覧

全部 `Run` のフィールドです。なので 1 つも隠れていません。各フィールドの詳しい説明は各パートのページにあります。

| パート | フィールド | 内容 | 確かめた範囲 |
|---|---|---|---|
| a | `pipe.enter`, `tiles`, `edge`, `moved` | 入るフレームは本物の機械、`base` の機械の上にある（数えるフレーム `t` は `base` のポーズでなく終わる `t` 番目のフレーム、定義。操作できる状態で始まることは証明: `Pipe.startE`、`Run.pipeStart₁`）。書き込みまでの各命令は `Clean`（`Run.pipeClean`、`chg.upCleanU` から）、右足の読みは `TilesOK`。書き込みまでに画面の端で位置を書かず、頭でブロックに当たらない。`P₂` は移動の終わり（`PlayerSubs`）の位置 | 本物の 68,311 フレーム、入る 177 回（[1 フレーム全部: ルーチンのバイトを書く命令](a-5-2-PipeWrites-ja.md)、[移動の終わりの位置](a-5-9-MoveEnd-ja.md)） |
| a | `pipe.opening` | 最初の 32 の数えるフレームのそれぞれについての条件（`RealB`: `map`、`after`、`afterV`、`page`。`noStore` は定理 `Real.noStore`、`lags.ctl` から。`after` は 3 バイト、速さとサブ速さが 0 で終わるときの向きとサブ速さ、速さを 0 にしないこと、当たりのビット、またはフレーム 32 で画面の左端。`afterV` は 6 バイト。各命令の `guardE` の `CleanK` は `Run.pipeReal`、`chg.upCleanU` から。縦のモデル、平らな地面、地面の高さ、ジャンプの長さは定理 `Real.vertOK`、`Real.flat`、`Real.ground_all`、`Real.jumpV`）。各フレームが出だしのモデルの 1 歩であることはここから証明（`move_model`、`CtrlKeep` の歩き）、フレーム 32 の終わりの上限も（`Run.pipeOpenB`） | TAS の 32 フレーム、自分の 300 回の 9,600 フレーム、早くポーズする 60 回の 1,856 フレーム（[本物のフレームでの出だし](a-5-4-OpenFrames-ja.md)） |
| a | `pipe.own` | フレーム 1 から `E` までは、そのフレーム自身の機械から読む。操作できるときの速さが 0 であることは証明（`Run.still`） | 本物の 434,206 フレーム（[土管までのフレームを機械から読む](a-5-5-PipeFrames-ja.md)） |
| a | `pipe.lags` | 数えるフレームは `base` のフレームのうちポーズでなく終わるもの（定義）。フレーム 1 から入るまで、ポーズは `dP` フレーム続かない（`lags.resume`）。数えるフレームは操作できる状態で終わる。操作から入るまでの各フレームの各命令は、数えるものも数えないものも `Clean` で、添字やポインタでポーズのバイトを書かない: `Run.lagsClean`、`chg.upCleanU` から。各フレームがアイドルループで始まること、数えないフレームがモードのルーチンを呼ばず 3 つの値を保ち操作できる状態で終わることは証明（`Lags.starts`、`lag_check`、`pause_check`） | 本物の 193,149 フレーム、入る 134 回（[操作から土管までの各フレームはアイドルループで始まる](a-5-5-3-2-StartRun-ja.md)）、範囲内の本物の 167,271 の数えないフレーム（[土管までの数えないフレーム](a-5-5-3-LagFrames-ja.md)）、51,711 の数えないフレーム（[ポーズで終わるフレームはモードのルーチンを呼ばない](a-5-5-3-3-LagPause-ja.md)） |
| b | `base.dA`, `dB`, `chg.ha₁`, `hb₁`, `ctlBy₁` | `base.seq` のどの機械が入るときと操作できるときか。`a₁` はフレーム 1 から最初に操作できない機械（定義 `Base.a₁`。`dA` はそこまでの上限）。`b₁` は `a₁` から最初に操作できる機械（定義 `Base.b₁`。`dB` はその上限。`ctlBy₁`: `a₁ + dB` で操作できる）。`ha₁`、`hb₁`: `a₁`、`b₁` での `lag` を除いた数 | 下の 2 つの走りで `route-check` |
| b | `chg.entryRest₁` | 入るとき: `EntryKeep.restNames` の 35 バイト（待ちの繰り返し、土管のタイマー、ほかの 74 バイトは `title`、`Run.upClean₁` から: `Run.entry₁`。各フレームが操作中に始まることは `Run.upStart₁` で証明） | 437 個の入る状態（[`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md)、[縦の土管に入るときの状態を、タイトルから出す](b-3-4-EntryKeep-ja.md)） |
| a, b | `chg.upCleanU` | 操作から縦の土管に入るまでのフレームの各命令は、4 つを合わせた 1 つのガードの `CleanK` を満たす: `EntryKeep` のもの（`EntryKeep.held` の 73 バイト（レベルの番号と大きさのビットを含む）、土管のタイマー、ポーズの 6 バイト）、`guardP`、`guardE`。合わせて 147 バイト（26 回目: 画面の左端。27 回目: スクロールへの足場の力）。ただの `CleanK` である（ROM の事実 `qCheck` は `EntryKeep.Checks` の 1 つ）。前の 4 つの条件は定理: `Run.upClean₁`、`Run.lagsClean`、`Run.pipeClean`、`Run.pipeReal`（[土管までの各命令に 1 つの条件](a-5-10-UpClean-ja.md)） | 本物の 221,490 フレーム、入る 40 回。入るまでに決まった物の枠を添字で埋める走りは定理の外 |
| b | `chg.places₁` | 土管のフレームの表の各場所で、点の数が上限以下で、機械がその場所の行のどれかを持つ | 437 個の走りの土管の全部のフレーム、3 種類の入力。証明はしていません |
| b | `chg.quiet₁` | 出口でポーズの音のキューが基準と同じで、鳴っていなければ 2 つの効果音と曲の段も（`QuietRest`）。画面のバッファは表の形。ポーズの音の種類は入口の `PauseV`（定理 `Run.entry₁`）から（[縦の土管のフレームを通るポーズ](b-3-7-2-PipePause-ja.md)） | Start を押した 1,002 の出口のうち 961（残り 41 は出口のフレームで解く） |
| b | `chg.noStart₁` | 土管のあとのゲームコアのフレームで Start を押さない | 入力についての条件。TAS では成り立つ |
| b | `chg.paused₁` | 切り替えの `lag` のフレームはポーズで終わる（`GamePauseStatus` の最下位ビットが立つ） | Start のある 995 + 823 の `lag` のフレーム、TAS のポーズ（[部屋への切り替えの `lag` のフレーム](b-3-3-LagPaused-ja.md)）。証明はしていません |
| b | `chg.time₁` | 縦の土管の入口でゲームのタイマーが 000 でない（`TimerOK`。土管のフレームが出口まで保つ: [縦の土管でのゲームタイマー](b-3-9-1-PipeTime-ja.md)）。`b₁` は定義から最初の操作。`left₁` が操作の前に 0 にならないことは証明 | 入る状態 15 個 × 3 種類、615 回の走り、TAS（[`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md)）。土管の中でポーズすると成り立たない（そのとき `quiet₁` も成り立たない） |
| c | `room` | 部屋のフレームの構造。各フレームは `CleanW`（プレイヤーのルーチンで覚えている速さは `\|v\|`、押す側はふさがれていない。`after`）か、止めて `ReadW`（当たりのビットは `collBits`。`Collide`）。`CleanR`、`ReadR` の残りは証明（部屋の歩き、フレームの時間、位置の範囲）。あいだのポーズで終わるフレームはモデルが読むバイトを保つ（`Run.roomKeep`、証明）。最初に立つまでの最初の落下と、立って始まるフレームは証明（`fall_long`、`vfall`、`floor_at`、`vfall_stand`、`air_in` はなくなった）。落下中に立ってから跳ぶフレームは最初の立ち（`stand_first`）と `wall` から証明し、`stand_wall` は前に状態 0 のフレームがあるときの立ちだけを求め、`C + 34` からはそのあとジャンプがないときだけ（1-1-c-7-5-22）。`stand_P` はなくなり、`stand_fast` は `hstep` に従う立ちか前に立ちがあるあとの立ちだけ（1-1-c-7-13-3、1-1-c-7-13-4）。`stop_run` はなくなり（1-1-c-7-4-2）、代わりに `ab_run`: `C + 37` から `C + 40` のジャンプのない地面のフレームが読む古い保存された速さは走りのしきい値より下。1 つ前のフレームがモデルに従うか、古い保存された速さか隠された向きでプレイヤーのルーチンに来るときだけ（1-1-c-7-4-3）。`ab_early` は落下の終わりからだけ（1-1-c-7-6-1）。33 回目から、どちらも隠された向きか空中で持ち越した古い保存された速さのあとだけ（1-1-c-7-4-4）。34 回目から `Off` はなくなった: 入るのは本物のフレームで `t0` の 12 フレーム以上あと。1 フレームのフィールド `offTop`、`offFloor`、`offNear`、`offSlow`、`offStand` を使う（1-1-c-7-8-2）。35 回目に `offStand` と `offFloor` はなくなった（1-1-c-7-8-3、1-1-c-7-8-4。`offFloor` は本物の走りで偽だった）。36 回目に `offNear` はなくなった（1-1-c-7-8-5: 部屋の歩きが入るフレームも追う）。`ab_early` の空中で左右なしの場合は隠された向きのあとだけ（1-1-c-7-6-2）。`late` は前に壁に当たったあとだけ（1-1-c-7-4-1）（`fall_jump` はなくなった）。床に着くフレームは証明。その移動の終わりの当たり判定を止める旗と縦のページも証明（`landQ` と `land_at` はなくなった）。落下のあとの床のフレームは証明。床から跳ぶか、移動の終わりからの足の判定で床にとどまる（`vfloor` はなくなった）。横が止まるフレームの入力はプレイヤーのルーチンで読む（`read_stop`）。ブロックの左側の床のフレームは証明（`low_floor_of`）、152 px かそれより下で終わるジャンプのフレームも証明（`low_jump_of`）、28 回目から 136〜151 px で終わるジャンプのフレームも証明（`push_one`、いちばん小さい余裕 `lowT`、`riseCheck`）。`low_at` はなくなった（1-1-c-7-5-19、1-1-c-7-5-20、1-1-c-7-5-21）。`facing` はなくなった。プレイヤーのルーチンから向きを追う部屋のフレーム全体の歩きが、すべてのフレームで証明する（`InRoom.face`、`Run.roomFace`。1-1-c-7-13-1、1-1-c-7-13-2）。`Approach.low` は大きなプレイヤーの最後の低いフレームが角の先にあってよい。求めるのは角かその先で、`low_jump` が証明するフレームのほかだけ（1-1-c-7-14-3）。速い跳びと遅い跳びは証明（1-1-c-7-14-1、1-1-c-7-14-2）。8 px と 11.5 px の間で始まるフレームは 8 px 以上で終わる（`farNear`）。フレーム、縦の状態、覚えている速さは機械から読む（`read_vs`、`read_ab`）。入るフレームは本物の機械で入る（`enters`）。`P(E)` はフレームの終わりで読む（`read_PE`）。そこでの位置は歩き `SideEntryEnd`、`SideEntryRest` から。その始まり（画面のバイトも）、`Clean`、タイル、頭が当たらないことは `Run.roomEnter` を通して `RoomMap` から。部屋の機械は `base` のフレーム `b₁` からのもの（定義: フレーム `n` は `seq(b₁ + ix(n − C))` で終わる。`ix(j)` は `seq(b₁ + k)` がポーズでない `j` 番目の `k ≥ 1`）。なので最初の機械は部屋で操作できる機械（`Run.roomCtl`）、入るフレームは `base` のフレーム `b₁ + ix(E − C) − 1`（`Run.roomEnter`） | TAS と本物の走り（[地下の部屋をつなぐ](c-5-RoomJoin-ja.md)、[本物のフレームと横のモデル](../0-0/0-3-2-FrameModel-ja.md)）（[部屋のブロックの地図](c-7-12-RoomMap-ja.md)、[横の土管に入るフレーム: 1 フレーム全部](c-7-16-SideFrame-ja.md)） |
| c | `roomLag` | 部屋で（`b₁ ≤ n < a₂`）ポーズで終わるフレームは `clock` の `lag` のフレーム | 部屋にポーズを入れたムービー 57 回（3,268 フレーム）、自分の入力 40 回（[部屋で一時停止する走り](c-7-1-4-RoomLag-ja.md)） |
| d | `base.dR`, `d₂`, `chg.ha₂`, `hb₂`, `ctlBy₂` | `a₂` は `b₁` のあとで最初にプレイヤーのルーチンを出た機械、`b₂` はそのあと最初に操作できる機械（定義 `Base.a₂`、`Base.b₂`）。そこまでのフレーム数の上限（`dR_pos : 1 ≤ dR`）。`a₂`、`b₂` での `lag` を除いた数 | 下の 2 つの走りで `route-check` |
| d | `chg.entry₂` | 入るときの 3 バイトが参照と同じ（エリア音楽のバッファ、イベント音楽のキュー、音の長さに足す数）。面の番号は縦の土管の入口から（`Run.area₂`、定理 `Run.area₁` から）。高さと画面のバッファの 5 バイトは入るフレームから（`Run.y₂` は `SizeKeep` の大きさから、`Run.buf₂` は `Run.ctl₂`、`Run.coin₂`、`Run.end₂` から。フィールド `buffer₂` は 26 回目からない: 1-1-d-2-5-5-4）。音楽の 5 バイトは部屋のフレームから（`RoomMusic.entryRest_of`）。ルーチンは部屋の入るフレームから（`Run.rt₂`）。ほかは部屋の歩きから（`ScreenPage.entry_rest`） | 部屋の 1 フレーム全部の歩きは入るフレームの終わりで `Entry2` の 90 バイトのうち 78 を知る（[部屋の画面のページと、横の土管の長いタイマー](d-2-4-ScreenPage-ja.md)） |
| d | `chg.roomLateU`, `roomLateS`, `roomRead`, `roomReads`, `roomOff₆` | 部屋の各命令での `SiteOK` の部分（読むタイル、ラウンド 34 から頭のためだけ: どの読みもリストのタイルを返すことは、歩きが部屋の最初の制御から運ぶブロックのバッファのタイルと、その中にある読みのアドレスから、[読みでのブロックのバッファのタイル](d-2-4-2-8-ReadTiles-ja.md)。ラウンド 35 から頭のマスが地図で空いていることだけ: そのとき読むバイトは空のタイルかコインで、歩きが運ぶ地図のビットから、[頭の読みを地図の頭のマスから](d-2-4-2-10-HeadFree-ja.md)。横の土管が読むときの位置の下のビット、ラウンド 34 で入るフレームだけ: その前のフレームは位置を読まない、[横の土管の位置の読みは入るフレームだけ](d-2-4-2-9-SideRead-ja.md)。ラウンド 35 で `roomRead` からもう 1 つの歩きで証明、`roomXbit` はなくなった、[横の土管の位置の読みを、頭のマスから](d-2-4-2-11-HeadSide-ja.md)。コインの消去は証明: ラウンド 30 で RAM の中でブロックのバッファの始め以降、ラウンド 31 で最初のブロックのバッファへのポインタなら終わりより前、[最初のブロックのバッファでのコインの消去](d-2-4-2-5-EraseSplit-ja.md)、ラウンド 32 でどのポインタでも、衝突のルーチンのプレイヤーの高さのテストから、`roomErase` はなくなった、[コインの消去の行](d-2-4-2-6-EraseRow-ja.md)、ラウンド 33 で同じことを歩きの中の高さと行の境界で、2 分の 1 から 3 分の 1 の表で、[境界からの消去の行](d-2-4-2-7-EraseRange-ja.md)）。時間（`Late`）については、ループの後ろへのジャンプがドット 9,000 までに走ることだけ。部屋の最初のフレームと、画面のバッファの制御 6 で始まるフレームの次のフレームでは画面の更新のレコードのループと音のルーチンのもの、ほかのフレームでは音のルーチンのもの（ラウンド 29: [部屋のフレームの時間](d-2-4-2-3-RoomLate-ja.md)。ラウンド 30: [ループの後ろへのジャンプからの時間](d-2-4-2-4-LoopTime-ja.md)）。`Reads` は画面の更新の画面のバッファへのポインタ越しで、部屋の最初のフレームと、画面のバッファの制御 6 で始まるフレームの次のフレームだけ。`Off` は制御 6 で始まるフレームの次の、制御 6 で始まるフレームだけ。`SiteOK` の残りは証明（`Run.roomSites`、ラウンド 27: [`SiteOK` の部分](d-2-4-2-1-SiteParts-ja.md)。ラウンド 28: [画面のバッファのレコード](d-2-4-2-2-BufferRecords-ja.md)）。`Room` は 1 つ目の切り替えの時間の段から（`Changes.roomAt`）、入るまでプレイヤーのルーチンにいることは `a₂` の定義から | 本物の 130,030 フレームと書き換えた走り（[部屋の画面のページと、横の土管の長いタイマー](d-2-4-ScreenPage-ja.md)）。自分の走り（[`SiteOK` の部分](d-2-4-2-1-SiteParts-ja.md)）。`LateS`: 自分の走り 107,546 フレームとムービーの 111 で、音のルーチンはドット 7,159 までに終わる（[部屋のフレームの時間](d-2-4-2-3-RoomLate-ja.md)）。後ろへのジャンプ: 自分の走り 1,156,371 フレームとムービーの 111 で、ドット 7,463 まで（[ループの後ろへのジャンプからの時間](d-2-4-2-4-LoopTime-ja.md)） |
| d | `chg.noStart₂` | 土管のあとのゲームコアのフレームで Start を押さない | 入力についての条件。TAS では成り立つ |
| d | `chg.paused₂` | 切り替えの `lag` のフレームはポーズで終わる | 土管のフレームで Start を押した走り 264 回の 46,829 フレーム（[地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md)）。証明はしていません |
| d | `chg.time₂` | 横の土管の入口でゲームタイマーが 000 でない（土管のフレームが出口まで保つ: [横の土管でのゲームタイマー](d-3-5-1-SideTime-ja.md)） | 本物の入口 210 回、本物の走り 132 回と、Start を押した 75 回（[地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md)）。`left₂` が操作の前に 0 にならないことは証明 |
| e, f | `pole` | 地上の 1 フレームごとの形（`frames`）、土台の近くの当たり判定、旗に触るフレーム（`touches`、`posKeep`、`bufAll`、`keepB`、`tilesCol`（`tiles` はなくなった: 1-1-f-6-17-2。`tilesRead` はなくなった: 1-1-f-6-17-3。`ySide` はなくなった: 1-1-f-6-17-4。`tilesFar` はなくなった: 1-1-f-6-17-5。`yKeep` はなくなった: 1-1-f-6-17-6。`keepB` と `bufAll` はプログラムで決まらない書き込みについてだけ書く: 1-1-f-6-17-7。29 回目: `tilesCol` は `TileCol` の代わりに `TileSlot` を求め（旗のタイルを読まないところでは多くを求める）、`TileCol` はフレームの上のエリアの解析の不変式からの定理。新しいフィールド `parWrap` を使う。そこでの左の端の評価は定理: 1-1-f-6-17-10。30 回目: `TileSlot` は読みの列を、旗のページの 2 つ前のページでだけ求め、`parWrap` はプレイヤーのルーチンに来るフレームにだけ求める: 1-1-f-6-17-11。31 回目: `parWrap` はなくなった（各フレームの厳しい規則を証明）。新しい `ctlU`（`UpdScrollVar` で画面のバッファの制御バイトが 6 でない、1 つの状態）。スクロールの量が高々 3 であることは、パート e の各フレームの読みからの定理 `PoleParserRun.amount_run`: 1-1-f-6-17-12。32 回目: `ctlU` は `UpdScrollVar` で解析が遅れているとき（`S + 3·N ≥ 32`）だけ求める: 1-1-f-6-17-13。33 回目: `tilesCol` の部分 (slot) は触るフレームの歩きの定理になり、`tilesCol` は旗の列での遠い読みで触るフレームの解析の列が旗の列まで来ていないことだけを求め、`bufAll` は、フレームの始まりの解析の列が旗の列まで来てから旗のタイルをブロックのバッファに書くことも求める: 1-1-f-6-17-14。`ctlU` は `S + 3·N ≥ 157` のところだけで求める: 1-1-f-6-17-15。34 回目: `bufAll` のその部分は、解析の列が旗の列まで来ているか、書き込みが解析の列の輪の列にあることだけを求める: 1-1-f-6-17-16。35 回目: `ctlU` はなくなり、`UpdScrollVar` で制御バイトが 6 でないことは、コインの地図を持つ各フレームの歩きの定理。新しい `coinBuf`、`readC`、`ctlKeep`: 1-1-f-6-17-17。`bufAll` は 34 回目の部分を解析の列の書き込みでないところでだけ求め、そこはブロックのバッファの列を追う歩きが証明する。新しい `bKeep`: 1-1-f-6-17-18。36 回目: `ctlKeep` と `bKeep` は、いくつかのポインタを通す書き込みとエリアの解析の 2 つのループでだけ求め（`bKeep` は触るフレームでルーチン、モード、タスクの最初の書き込みのあとでも）、ほかは各フレーム全体の歩きの定理: 1-1-f-6-17-19）、`edge`。`moved` は定理 `Run.moved`。`keep.noStore`: 触る前のフレームはルーチン、モード、タスクを番地で書かない。`keep` の最後のフレーム、1 フレーム全部の歩き `PoleFrame`）、城の旗。城までのフレームは定義から `base` の数えるフレーム（`toCastle`）。`keep.cleanE`: 各命令は `guardE` の `CleanK` を満たす（`frames.spareE` はなくなった。26 回目: `guardE` は画面の左端も守る。27 回目: スクロールへの足場の力も守る。29 回目: エリアの解析の 4 つのバイトも守る）。地上のフレームは機械の上の定義 `frOf`（`fr`、`frames.reads` はなくなった）で、`frames` のフィールドは `state`、`collide`（`CollideS`。3 つ目の場合は、右への押し戻しを基点（フレームの始まりの位置と画面の左端の大きい方）から押さえる。フィールド `OnFrames.endKeep` と `OnFrames.sideW` を使う（33 回目: `sideW` は横のタイマーに届きうる書き込み（ある添え字が元のアドレスをタイマーに運ぶ、絶対アドレスに添え字を足した書き込みか、ポインタを通した書き込み）でだけ求め、ほかの命令は定理 `PushTimer.sideW_far`。また横のタイマーが押し戻しの値で終わらないどのフレームでも求める: 1-1-e-2-10-3-22。34 回目: `sideW` はそのような書き込みのうちエリアの読み込みのコードと頭がブロックに当たるときのコードにあるものでだけ求め、ほかは定理 `SideRange.near_side`（添え字のレジスタの範囲を知る歩き）: 1-1-e-2-10-3-24。35 回目: `sideW` はそこのポインタを通した書き込みと城の行のループの書き込みでだけ求め、ほかは定理 `SideLoop.near_side`: 1-1-e-2-10-3-25。36 回目: `sideW` は `SideAcross.FactsAt`（ブロックのバッファの列と `SprDataOffset_Ctrl`。このフレームではパート f のフィールド `bKeep` と `keepB` がそれを与える: `SideAcross.Run.factsAll`、ルートはまだ使わない）のないフレームでだけ求め、ほかのフレームは定理 `SideAcross.near_sideA` で、新しいフィールド `castleRow`（城の始めの行は高々 10、城のループでの `sideW` のかわり、そこでは弱くない）を使う: 1-1-e-2-10-3-26。32 回目: `endKeep` はフレームの終わりの場所のバイトだけを求める。横のタイマーが高々 1 で終わるフレームでのスクロールの処理のあとの彼のピクセルは定理 `PushTimer.pix_end`。`sideW`: スクロールの処理のあと、添え字かポインタを通した書き込みは横のタイマーを書かない: 1-1-e-2-10-3-20。31 回目: 右端と左端の関係と左端のページは定理 `OnFrames.relAll`、`OnFrames.pageAll`。`endKeep` は右への速さを保たないフレームだけでピクセルを求める: 1-1-e-2-10-3-19。30 回目: 画面の外のビットのルーチンで右端は左端の 255 px 右にある。スクロールの処理の戻りのあと、押し戻しか補正を呼ぶフレームでは彼のピクセルは変わらず、描画が場所のバイトを書く。`OnFrames.nearStep` は定理 `OnFrames.nearStepAt`: 1-1-e-2-10-3-18。29 回目: 数えるフレームのそれぞれが始めから終わりまで `NearM` を保つ。`OnFrames.nearA` は定理 `OnFrames.nearAAt`: 1-1-e-2-10-3-17。28 回目: 前のフィールド `OnFrames.near` は定理 `OnFrames.nearAt`: 1-1-e-2-10-3-16。27 回目: 足場の力は 0、1-1-e-2-10-3-14。前のフィールド `OnFrames.edge₀` と `OnFrames.edge` は定理 `SurfaceFrames.edge_zero`: 1-1-e-2-10-3-11 と `OnFrames.edgeAt`: 1-1-e-2-10-3-13）。23 回目に、フレームの始まりの位置からの前の形が、画面の左端より 1 px 左で始まるフレームのあとの本物のフレームで偽だと分かり、24 回目に直した: 1-1-e-2-10-3-10。位置は押し戻しか補正を呼ぶフレームにだけ求める。右へ動いて速さを保つフレームと呼び出しのないフレームの位置は定理 `OnFrames.keepAt`、`OnFrames.stillAt`）、`posW`、`clampR`（スクロールの処理からあとの 1 命令ずつの条件: 位置を番地で書くのは押し戻しと補正の内側だけ、その外で添字かポインタで書く命令は位置を書かない。右へ動いて速さを保つフレームで、補正のときに右へ動いているなら、補正先は位置）、`moves`（`Moves.stop`。28 回目から P(Q) で終わるフレームだけ。32 回目から、スクロールの処理で彼が画面の左端より右にいるか、フレームが左端より左で始まるときだけ: それ以外のフレームは定理 `OnFrames.stopAt`: 1-1-e-2-10-3-21。33 回目から、押し戻しのあるフレームだけ（スクロールの処理で端より右で終わりで横のタイマーが押し戻しの値、または始めで端より左でそこでタイマーがその値）: `OnFrames.stopRight`、`OnFrames.noStopRight`、`OnFrames.leftEnd`、`StopClamp.stop_clamp`: 1-1-e-2-10-3-23。`AfterP.stop` は定理 `StopAt.stopP`。`AfterP.keep` は定理 `OnFrames.keepAt`: 1-1-e-2-10-3-8）、`faceJ`、`vAfter`（縦の 5 つのバイト）、`box`（`coll`、`farLate` はなくなった。`spareC` と `spareV` は `keep.cleanE` の一部。`vAfter` の 4 つのバイトは定理 `OnFrames.kAt`、縦の力は `OnFrames.vfAt`。スクロールの処理からあとの向き、サブ速さ、右へ動くときの当たり判定のビットは `FaceKeep` の定理。745 フレームより後に触る走りはフレームの数から: `SurfaceLate`）。触るまでのフレームは `base` のフレーム `b₂` からのもの（`keep` の定義: `all n = seq(b₂ + n)`）。なので最初の機械は操作できる機械（`Run.atCtl`）。速いジャンプの前の覚えている速さは機械から読む（`Run.stop_step`、`Run.stored_step`。`stopped`、`onGround`、`ground` はなくなった）。`reads` は残る | 本物の走り（[地上: 操作できてからのフレームを 1 つずつ](e-2-SurfaceFrames-ja.md)、[旗に触るフレームを本物のフレームで](f-6-1-PoleEntryRule-ja.md)、[操作から城まで](f-5-PoleJoin-ja.md)） |
| 全体 | `clock`, `z₁`, `z₂` | 全部のフレームの種類とカウンタ。1 フレームごとの規則と、どのフレームがどのパートか | ポーズを入れた走りを含む 7 つの全部のフレームと、TAS（[城から 1-2 まで](g-1-CastleToLevel-ja.md)） |
| 全体 | `title` | タイトルで Start を押すところ（`title.boot`）: 走りが電源から来る（1 つの状態: 電源を入れたときの機械。RAM は分からないが、ウォームブートの印がないか 2 バイトが 0。押す前に Start も Select もない。フレーム 31 から 508 で Start、A はあってもよい。`power`）か、前に Start があってよく Select のないまま、フレーム 31 から 508 で最初にタイトルを出る（`menu`）か、最初のデモのあとのフレーム 1657 から 2123 で押す（`later`）か、押したフレームのあとの機械が何もしないループにいて、走りが書く前に読む 51 バイト、ポーズの音のバッファ、レベルの番号が基準の機械と同じで、タイマーを読み込ませるフラグが 0 でない（`press`）。初めの 3 つの場合、この条件は証明済み（`TitleStart.Begin.press`）。フレーム 0 でゲームコアなら Start を押さない（それより前は Start を押してポーズしてよい）。フレーム 0 は最初に操作できるフレームの前のフレーム。ここから、フレーム 0 はタイマー `t0`、位相 2 で始まり、操作できるときの速さは 0（`Run.zero`、`Run.still`。この 2 つはフレーム 0 の条件を使わない） | TAS と本物の 339 通り: タイトルの何フレーム目かの Start、タイトルでの任意のボタン、A と Start、ゲームコアでのポーズ、ゲームオーバーのあと、ゲーム中のリセット（`title-check`）。電源からは元の組の 566 通り、出る前に Start がある 600 通り、最初のデモのあとの 100 通り（`title-boot-check`、`title-menu-check`）（[タイトルの Start から操作できるまで](0-5-3-TitleStart-ja.md)、[電源から Start を押すまで](0-5-4-TitleBoot-ja.md)） |
| 全体 | `read₀` | `clock` のフレーム 0 の前のカウンタは、フレーム 0 が始まるときの機械のもの | 列の作り方から |
| 全体 | `base`（`seq`、`inp`、`next`） | 走り全体の本物の機械の列 1 本。番号は `clock` と同じ。`pipe`、`room`、`pole`、`chg` はこの列から機械をとる | 列の作り方から、どの走りでも成り立つ |
| 全体 | `flag`, `L` | 城に入ったあと面の読み込みが終わった最初のフレーム `G` の本物の機械の条件 `Good`、その前のフレームの規則（`pre`）、城に入った直後の処理 2、旗の高さ、`T`、`c`、フレーム `L` のあとレベルの番号が変わる | `G` からのフレームの規則と処理 5 は、どんな入力でも証明。ポーズで終わるフレームは `lag` のフレームでカウンタを保つ（`flag.noStart` はなくなった。[城に入ったあとの星の旗の規則](g-2-1-FlagRule-ja.md)、[城に入ったあとのポーズ](g-2-5-FlagPause-ja.md)）。条件は TAS、遅く触る走り、本物の花火、Start ありとなしの乱数、ポーズ、タイマーを書き換えた走りで確認。城に着く乱数の入力の走り 193（触る高さ 51 通り）のうち 176 で `G = E + 1`（[城に入ったときの条件を広げる](g-2-2-1-FlagWide-ja.md)）。残りの 17 では読み込みが動いていて、`G = E + 1 + k`（`k` は 1〜9）。`pre` はそのフレームで成り立つ。種 1001〜3000 のこのような走り 20 でも成り立つ（[面の読み込みが動いている城の入り](g-2-2-3-FlagParser-ja.md)） |

`E = C_s + c + j`、タイマーの式、格子の式は `Run` のフィールドではなくなりました。`clock` から証明します（`Run.hE`、`Run.hT`、`Run.hc`）。フレーム 0 の前のタイマーと位相は `title` と `read₀` から出します（`Run.zero`、`Run.s_zero`、`Run.ph_zero`）。`D ≥ 33` とレベルが変わるフレームの式は `flag` から証明します（`Run.hD`、`Run.hL`）。`change₁` と `change₂` もフィールドではなくなりました。`chg` から証明します（`Run.change₁`、`Run.change₂`）。`level_ge_of_parts` はこのほかに `2 ≤ q` を使います。ゲームの値で計算して確かめます。また ROM での確かめ `pipe_end`、`side_bound`、`side_end`、`side_start`、`side_ctl`、`room_start`、`RoomChecks`（`screen_facts`、`screen_timer_same`、`screen_rt`、`pipe_end`、`screen_start`）、`flag_checked`、`title_check` と、星の旗の待ち時間が 6 以上であることを使います。これらは非公開の定理で、仮定ではありません。

`route_1_1` は `Merge`、`GMerge`、`Cond`、H3 を使いません。`Run` のフィールドにも定理の引数にもありません。6 個の物が近くに集まらないことも使いません。これらはちょうどの長さの定理のものです。ただし `lag` のフレームはポーズで終わること（`paused₁`、`paused₂`）を仮定するので、切り替えの中でポーズでない `lag` のフレーム（はみ出したフレームの次など）がある走りは定理の外です。本物の走りでは、切り替えの中ではみ出すのは RAM を消すフレームだけで、その次は数える `setup` のフレームです。

`Run` の形から、次の走りは定理に入っていません。

* 2 つの土管を通らない走り。歩いて行くと遅いことは、この定理の外です。
* 大きいマリオ、パワーアップのある走り。パワーアップはゲームを 59 フレーム止めるので、数の部分は `level_ge_of_late` にあります。つなぐのはまだです。
* 旗の近くに敵がいる走り、旗を越えて戻ってくる走り。
* 入るフレームが書き込みまでに、画面の端で位置を書くか、頭でブロックに当たる走り（`pipe.edge`）。
* 触る前の地上のフレームが、ルーチン、モード、タスクを番地で書く走り。パワーアップ、ダメージ、死ぬ、土管、つる、斧、面の切り替え、それより前の触りのどれかです（`pole.keep.noStore`）。
* 触るフレームが書き込みまでに、画面の端の書き込みで旗の範囲に入る走り（`pole.edge`）。
* 触るフレームが書き込みまでに、移動のルーチンの添字 0 の書き込みのほかで、添字かポインタを通して位置を書く走り（`pole.posKeep`）。
* 操作から縦の土管までの数えるフレームが、操作できない状態で終わる走り。大きくなる、けが、死ぬ、のどれかです（`pipe.lags.ctl`）。
* 縦の土管に入るまでに、決まった物の枠（敵の枠 3 と 6、ファイアボール、ブロック 2 と 3 など）を添字で埋める走り（`chg.upCleanU`）。
* 縦の土管のあとのゲームコアのフレームで Start を押す走り（`chg.noStart₁`）、出口のフレームでポーズを解くか、表にない曲や画面のバッファがある走り（`chg.quiet₁`）、土管のフレームで次の敵が読み込まれるなど表の行にない走り（`chg.places₁`）、入るときファイアマリオの走り（`chg.entry₁`、`chg.roomStart`）。
* 横の土管のあとのゲームコアのフレームで Start を押す走り（`chg.noStart₂`）。測った走りではそこでのポーズは操作を遅らせるだけですが、Lean では示していません。
* 切り替えの中に、ポーズで終わらない `lag` のフレームがある走り（`chg.paused₁`、`chg.paused₂`）。
* 城に入ったあと面の読み込みが終わった最初のフレームの機械が `Good` に入らないか、その前のフレームが規則に従わない走り（`flag.entry`、`flag.pre`）。測った 583 本の走り（動画、ポーズ、種 1〜3000 の乱数の入力）にはありません。`pre` は証明していません。
* タイトルで押したあとの機械が条件を満たさない走り（`title.boot` の場合 `press`）で、[電源から Start を押すまで](0-5-4-TitleBoot-ja.md) の電源からの走りでもないもの。操作できるまでの Start とポーズは入ります。
* 横の土管で `chg.entry₂` を満たさない走り。時間切れが近いときの音楽が鳴っている、ファイアボールが生きている、ブロックの物が生きている、入るフレームがはみ出す、のどれかです。音楽の場合は、別の定理が 1-2 は 1748 フレームより前に始まらないことを示します（[急ぎの音楽が鳴る走り](0-6-4-HurryMusic-ja.md)。音楽を始める最初のフレームと、その前の操作中のフレームの仮定 `start`、`bLe`、`noStore`、`clean`、`below` のもと）。この土管までに 1-1 のパワーアップは 1 つだけですが、Lean では示していません。

## 2 つの切り替え（`chg`）

`base` には本物の機械の列が 1 本あります。`seq n` はフレーム `n` が始まるときの機械で、`seq (n + 1)` はフレーム `n` が残したものです。`clock` と同じです。`r(n)` は `n` より前の `lag` でないフレームの数です（`seen`）。

```
seq(n + 1) = frame(seq n, inp n)
r(a₁) = E_a + 1,   r(b₁) = C_r + 1,   r(a₂) = E_b + 1,   r(b₂) = C_s + 1
entryRest₁ : Rest(seq a₁)                 b₁ = firstCtl(seq, a₁, dB)   ctlBy₁ : ctl(seq (a₁ + dB))
a₁ = 1 ≤ n ≤ 1 + dA で最初の ¬ctl(seq n)      upCleanU : 1 ≤ n < a₁ → ∀ j, CleanK(GU, q, trₙ(j))
a₂ = 最初の n ≥ b₁ で rt(seq n) ≠ rt(r)      b₂ = 最初の n ≥ a₂ で ctl(seq n)      ctlBy₂ : ctl(seq(a₂ + d₂))
entry₂ : EntryRestM(seq a₂)
roomRead : b₁ ≤ n < a₂ → ∀ j, HeadFree(trₙ(j))      （ラウンド 35: HeadFree(m) := pc(m) = 読み → save(m) ∈ heads → M(addr(m) & 0x7FF) ∈ {空, コイン}、M は地図、ReadH の代わり。roomXbit はなくなった、roomRead と HeadSide の歩きから。ラウンド 34: ReadH(m) := pc(m) = 読み → save(m) ∈ heads → val(m) ∈ {空, コイン}、Read の全体の代わり。Xbit は部屋のすべてのフレームの代わりに入るフレームだけ。ラウンド 32: roomErase、EraseTwo(m) := pc(m) = 消すところ → 2 つめのブロックのバッファの始め ≤ ptr(m) & 0x7FF → addr(m) & 0x7FF < ブロックのバッファの終わり、はなくなった）
roomLateU : b₁ ≤ n < a₂ ∧ U(n) → ∀ j, LateS(scrQ, trₙ(j))      roomLateS : b₁ ≤ n < a₂ ∧ ¬U(n) → ∀ j, LateS(sndQ, trₙ(j))
      （U(n) := n = b₁ ∨ (b₁ < n ∧ c(seq(n − 1)) = 6)。LateS(q, m) := q(pc(m)) → dot(m) ≤ 9,000。sndQ(p) := SoundEngine ≤ p ∧ back(p)。
       scrQ(p) := sndQ(p) ∨ (RepeatByte ≤ p < UpdateScreen + 16 ∧ back(p))。back(p) := p の命令は負のオフセットの分岐か、p 以下のアドレスへの JMP）
roomReads : b₁ ≤ n < a₂ ∧ (n = b₁ ∨ (b₁ < n ∧ c(seq(n − 1)) = 6)) → ∀ j, ReadsAt(Z₁, trₙ(j))      roomOff₆ : b₁ < n < a₂ ∧ c(seq n) = 6 ∧ c(seq(n − 1)) = 6 → ∀ j, Off(trₙ(j))
paused₁ : a₁ ≤ n < b₁ ∧ kind(n) = lag  →  Paused(seq(n + 1))
time₁ : Timer(seq a₁)
places₁ : a₁ ≤ n < b₁ ∧ inPipe(seq n)  →  ∀ j, Places(trₙ(j))
noStart₁ : a₁ ≤ n < b₁ ∧ coreFrame(seq n)  →  inp n に Start はない
quiet₁ : a₁ ≤ n ≤ b₁ ∧ ExitAt(seq n)  →  QuietRest ∧ Shape (seq n)
paused₂ : a₂ ≤ n < b₂ ∧ kind(n) = lag  →  Paused(seq(n + 1))
noStart₂ : a₂ ≤ n < b₂ ∧ coreFrame(seq n)  →  inp n に Start はない
time₂ : Timer(seq a₂)
```

パートは機械を `base` からとるので、`Run` の前のつなぎは定理です:

```
フレーム 1 のバイトは土管の数えるフレーム 1 のもの               Run.pipeKeep₁   （その前のフレームはポーズで終わり、バイトを保つ）
room.fe C_r = seq b₁                                         Run.roomCtl     （room.fe n = seq(b₁ + ix(n − C_r))、定義）
b₁ < a₂                                                      Run.b₁_lt_a₂（Room(seq b₁)、dR_pos）
1 ≤ n < a₁ → ∀ j, Clean(trₙ(j))                             Run.upClean₁（upCleanU から）
area(seq a₁) = area(e₁)                                      Run.area₁（Run.entry₁ から。e₁ = 縦の土管の入口の参照の機械）
area(seq a₂) = area(e₁)                                      Run.area₂（パート b の段からの Run.areaB₁ と、AreaKeep の部屋の歩き）
y(seq a₂) = y(e₂),  Buffer(seq a₂)                            Run.y₂、Run.buf₂（SizeKeep の大きさ、Run.ctl₂、Run.coin₂、Run.end₂ と、入るフレームの歩き）
rt(seq a₂) = e_s                                             Run.rt₂（room.enters、Run.roomEnter、EntryRoutine.rt_of_rows）
k = b₁ + ix(E_b − C_r) − 1,  b₁ ≤ k < a₂,  room.fm(E_b − 1) = seq k     Run.roomEnter   （E_b − C_r ≤ ups: Run.roomMany、roomLag から）
pole.seq 0 = seq b₂                                          Run.atCtl       （keep.all n = seq(b₂ + n)、定義）
1 ≤ E_a                                                      Run.pipeOne     （pipe.fm 0 = seq 0。フレーム 0 は操作できる状態で終わり、入るフレームは土管のルーチンで終わる）
```

ここから:

```
E_a + 91 ≤ C_r                                               Run.change₁（PipeRun.bound と pipe_end）
a₁ ≤ n < b₁ → left₁(seq n) ≠ 0                              Changes.first₁（time₁ と定理 Changes.ctlFirst₁）
Room(seq b₁)                                                 Changes.roomAt（時間の段と screen_start）
PauseV(seq a₁)                                               Run.entry₁（EntryKeep.entryV_of_title）
g(seq b₁) & 0x7E = 0                                         ChangesK.pauseBits₂（最初の切り替えの段と pause_index）
EntryRest(seq a₂)                                            ChangesK.entryRest₂（音楽の表を運ぶ部屋の歩きと entry₂）
Entry2(seq a₂)                                               ScreenPage.entry_rest（Room、SiteOK、EntryRest）
timer(seq a₂) ≥ 160                                          ScreenPage.entry_long（Room と RoomChecks）
StartAt(room.fe room.C)                                      Run.roomStart（pipe_end と room_start）
vsOf(room.fe C_r) ∈ rN.vStart                                Run.roomV0（pipe_end と room_vert の段）
─────────────────────────────────────────
a₂ ≤ n < b₂ → left₂(seq n) ≠ 0                              EndRun.firstF（time₂ と b₂ の定義）
E_b + 282 ≤ C_s                                              Run.change₂（EndRun.bound と side_bound、side_end）
```

`left` はフレームの境目で読みます。ルーチンがはみ出すフレームはルーチンの途中で終わり、次のフレームが `lag` のフレームです。

**`lag` のフレームは `left` を変えません。** `keep₁`、`keep₂` は仮定ではなくなりました。`lag` のフレームがポーズで終わること（`paused₁`、`paused₂`）から、ROM の確認が `left` は減らないことを出します。下は前の測定です。 各切り替えで、インターバルタイマーの位相が動かないフレームのうち、`left` が減るのは 1 つだけで、それが `setup` です。これは数えるフレームで、その番号が `z₁`、`z₂` です。ほかのそういうフレームでは `left` は変わりません。`change-scenes` は、本物の入る状態から、入力なし、ランダムな入力、Start を 2 回、はみ出すように 6 個の物をあるフレームに書いた場合で、これを示します。

| 切り替え | 走り | フレーム | はみ出した走り | `lag` のフレーム | `left` が減った `lag` のフレーム | `left` が 2 以上減ったフレーム | 操作までの最小（`lag` を除く） |
|---|---|---|---|---|---|---|---|
| 地下へ | 237 | 24,767 | 67 | 3,200 | 0 | 0 | 91 |
| 地上へ | 356 | 125,628 | 54 | 26,176 | 0 | 0 | 282 |

調べていないこと:

* フレームがはみ出したのは、物を書き込んだ状態だけです。書き換えのない走りでは、切り替えの中のこういうフレームは、ポーズのほかは `setup` だけです。
* 地上への切り替えの最後の 122 フレームでは、6 個の物を書いてもはみ出しませんでした。ここの `lag` の規則はポーズでだけ確かめました。

これらのフィールドは 1 フレームごとの仮定で、証明していません。`pipe`、`room`、`pole`、`chg` は機械を `base` からとるので、定義でつながっています。つながっていないもの: `clock` の種類が機械と合うのは、フレーム 0（`read₀`）、城に入ったあと（`flag`）、`paused₁`、`paused₂`、数 `ha₁`、`hb₁`、`ha₂`、`hb₂` だけです。なので `clock` の城に入るとき `E`（`flag` が機械を読むところ）が `pole` の城に入るとき `c`（`atCastle` が読むところ）だとはわかっていません。`pole.seq` そのものは `base` から読みます（`FrameKeep.Keep.seq`）。[地上で](0-5-2-1-CastleJoin-ja.md): `b₂` から `E` までの各フレームが、ポーズで終わるときにちょうど `lag` フレームなら（`Run.LagUp`、フィールドではない）、`E` は `pole` の数えるフレーム `c` で（`Run.castle_join`）、`atCastle` は `flag` から出ます（`Run.atCastle_of_flag`）。城までの 646 の走り、地上の 276,544 フレームで成り立ちます。

## 仮定が空でないこと

`route-check` は、本物のフレームから `Run` の数を読みます。

| 走り | 操作の変わり目 | 触る | 城 | T | E + T | 1-2 |
|---|---|---|---|---|---|---|
| TAS | 368, 459, 570, 852 | 1092 | 1218 | 370 | 1588 | 1748 |
| TAS の 1089 のあと、左、A、A、A | 368, 459, 570, 852 | 1093 | 1219 | 369 | 1588 | 1748 |

どちらも数の仮定を全部満たし、`L` は式と一致します。`route-check` は `chg` も読みます。`a₁, b₁, a₂, b₂` = 369, 460, 571, 853 で、`lag` を除いて 1 を引くと 368, 459, 570, 852 です。入るときの `left` は 91 と 282 で、条件はどちらも成り立ちます。`z₁, z₂` = 418, 732 で、位相が動かないほかのフレームはなく、`left` が 2 以上減るフレームもありません。つなぎも確かめます。フレーム 1 は数えるフレームで、部屋の入るフレーム `b₁ + (E_b − 1 − C_r)` はどちらの走りでも 570 = `a₂ − 1` です。100（縦の土管の前）、380、416、450、575、730、845 のポーズでも `a₂ − 1` です。`changes-check FM2 pause F D` は、380、416、450、575、730、845 のポーズで同じ数を、50 または 60 の `lag` のフレームとともに出します。切り替えの中には Start を受けつけないフレームがあり、そこではムービーがずれて、確認は 2 つめの切り替えを終えずに終了コード 1 で終わります。`clock` の規則は、どちらの走りでも全部のフレームで成り立ちます（作業用のプログラム）。地上の構造は `pole-join-check` で、同じ走りに成り立つことを確かめました。部屋の構造は TAS について、リポジトリに入れていない作業用のプログラムで確かめました。全部のフィールドを Lean の項として TAS から作ってはいません。

## いちばん危ない場合

和 `E + T` に余裕はありません。1 小さいと 1-2 は 1727 です。和を 1 小さくする場合が 1 つだけあります。

```
g = 241,  W = 125   →   E = 1218,  T = 369,  和 1587
```

`W = 125` は実際に起こります。左に動いていない遅いジャンプで、端数が 176/256 ピクセル以上のときです（位置を書き換えた本物のフレーム）。これを除くのは `slow_tight` で、`g ≤ 241` では前のフレームで左に動いていて端数が 176/256 ピクセルより小さいことを示します。このとき `W ≥ 126` であることは `flagTight` の仮定で、測定です。

土台の高さの落下が 3 フレーム以下であること（`fall`、`fallCheck`）もここで使います。

TAS の 1085 の状態から位置を 16/256 から 160/256 ピクセルまで 10 通り動かし、A、B、左、右の全部の入力で 1093 まで調べました。1092 と 1093 のどの触りも `W ≥ 126` でした。

## 再現

```
python3 prove.py                                      # 全部の定理の確認
.lake/build/bin/smbrta route-check FM2                # 全体の数
.lake/build/bin/smbrta route-check FM2 1089 02808080  # 1 フレーム遅く触る走り
.lake/build/bin/smbrta changes-check FM2 pause 380 60 # ポーズを入れたときの chg のフィールド
.lake/build/bin/smbrta change-scenes FM2              # ランダムな入力、ポーズ、はみ出すフレームでの left
.lake/build/bin/smbrta frames-check FM2                # clock と flag の規則を全部のフレームで
.lake/build/bin/smbrta pipe-rule-check FM2             # pipe のフィールドを本物のフレームで
.lake/build/bin/smbrta side-end-check FM2              # 出口の条件と、そのあとの left を本物のフレームで
.lake/build/bin/smbrta pole-join-check FM2 1089 02808080
.lake/build/bin/smbrta touch-search-at FM2 1085 80 8  # 位置を動かして、触ったフレームごとの城までの長さ
```
