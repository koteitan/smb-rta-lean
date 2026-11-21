[← Back](README-ja.md) | [English](d-2-5-3-AreaKeep.md) | [Japanese](d-2-5-3-AreaKeep-ja.md)

# 縦の土管から横の土管までのレベルの番号

**主張.** 縦の土管の入口でレベルの番号（`AreaNumber`）が基準の入口の値なら、横の土管の入口でもその値です。証明しました。16 回目から、縦の土管の入口から部屋の最初の操作まではパート b の歩きがこのバイトを運びます（出口の一覧にこのバイトがある）。部屋のフレームの 1 つの歩きが横の土管の入口まで運びます。そこで `Route.Run` は横の土管の入口で 10 バイトでなく 9 バイトを求めます（`chg.entry₂`、1-1-d-2-5）。14 回目にこのバイトは縦の土管の入口へ移り（`area₁`）、15 回目からそれも定理です（1-1-b-3-4-5）。

このページは、この回のほかの 2 つの候補について測ったことも書きます。足す音の長さ（`NoteLengthTblAdder`）と、横の土管の入口でのゲームタイマー（`chg.time₂`）です。どちらも部屋のフレームを通りません。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は入力 `i` での `m` の 1 フレーム、`trₙ(j)` はフレーム `n` の `j` 命令目の機械です。`seq(n)` はフレーム `n` が始まるときの機械です。`a₁`、`b₁`、`a₂` は縦の土管の入口、部屋の最初の操作、横の土管の入口です（`Route.Base`）。`i` はレベルの番号の番地、`e` は縦の土管の基準の入口、`v := e[i]` です。`S[i ↦ v]` は、`i` も値 `v` で知る抽象の状態 `S` です。`rt(m)` はルーチンのバイト、`r` は部屋の基準の機械です。

## 定理

`baseK` は縦の土管のフレームの歩きの出口の状態です（[部屋への切り替え](b-3-2-PipeChangeEnd-ja.md)）。`timeRows` は出口からのパート b の段のうち `left` が 0 のものです（[音のバイトを表で運ぶ](b-3-7-1-SoundRows-ja.md)）。`InRowsT(m)` は `m` がそこに入ることです。

```
i ∈ exitNames                                     （16 回目。入口の一覧には 15 回目から i がある）
roomCheck :  …  ∧  ∀ row ∈ timeRows, ∀ S ∈ row:  S は i を値 v で知る

area_of_rows :  InRowsT(m)  →  m[i] = v
Run.areaB₁   :  seq(b₁)[i] = v                                           （定理）
area_run     :  Room(seq c),  seq(c)[i] = v,
                ∀ n ∈ [c, e):  (∀ j, SiteOK(trₙ(j))) ∧ rt(seq n) = rt(r),     rt(seq e) ≠ rt(r)
                →  seq(e)[i] = v

Run.area₁       :  seq(a₁)[i] = v                                        （15 回目から定理、1-1-b-3-4-5。14 回目はフィールド）
Run.area₂       :  seq(a₂)[i] = v                                        （定理）
entryAt_of_area :  m[i] = v  ∧  EntryAt(R₉, m)  →  EntryAt(R₁₀, m)
chg.entry₂      :  EntryAt(R₉, seq a₂)                                   （9 バイト。前は R₁₀）
```

`R₁₀` は `restIdxR` の 10 バイト、`R₉ := R₁₀ \ {i}` です（`restIdxA`）。`EntryAt` は [横の土管の入口のルーチン](d-2-5-2-EntryRoutine-ja.md) のものです。

**出口の一覧.** 縦の土管のどのフレームもこのバイトを書きません。入口の条件はこのバイトを知ります（15 回目）。だからパート b の土管のフレームの歩きは、このバイトを知る状態で終わり、出口の一覧にこのバイトを入れられます（`PipeChangeEnd.exitNames`、16 回目）。出口のあとの段は出口の状態（`baseK`）から始まるので、段もこのバイトを知ります。`ScreenStart.roomCheck` はもう 1 つ求めます。`timeRows` の各状態がこのバイトを値 `v` で知ることです（`rowsArea`）。

**`Run.areaB₁`.** 最初の切り替えのパート b の走り（`ChangesK.run₁`）は、部屋の最初の操作 `b₁` の機械を `timeRows` に入れます（`PipeRunK.inRowsT`）。`area_of_rows` がそこでのバイトを出します。

14 回目と 15 回目には、ここにバイトを知るパート b の歩きの写しが 2 つありました（入口から出口までの `pipeCheckA`、ネイティブで 15〜18 秒。段の `rowsCheckA`、116〜136 秒）。なくなりました。

**`area_run`** は 1 つの状態の表 `[(i, v)]` での `RoomPause.pause_run` です。音のルーチンの区間では、歩きは表からバイトを知ります。区間の外では、バイトを書くかもしれないステップで歩きは失敗します。

**`Run.area₂`.** `Run.areaB₁` が `b₁` でのバイトを出します。`b₁` から `a₂` までの `area_run`（`b₁` での部屋の条件、`roomSites`、`roomStay`、`a₂` でほかのルーチンになることに `Run.rt₂`）が `a₂` でのバイトを出します。

Lean: `Theorems/AreaKeep.lean`（`areaI`、`regA`、`cfgA`、`roomCheckA`、`smallCheck`、`roomOK_of_check`、`area_run`、`Facts`、`factsOf`、`small_parts`）、`Theorems/ScreenStart.lean`（`rowsArea`、`roomCheck`、`area_of_invL`、`area_of_rows`）、`Theorems/PipeChangeEnd.lean`（`exitNames`）、`Theorems/Route.lean`（`restIdxA`、`RoomChecks.area`、`Run.area₁`、`Run.areaB₁`、`Run.area₂`、`entryAt_of_area`、`Run.chgK`）、非公開の `Proof/AreaKeep.lean`（`area_room`、`area_small`、`area_factsA`）と `Proof/AreaJoin.lean`（`area_facts`）。公開のファイルにゲームのデータはありません。

## 確認

| 確認 | 歩くもの | 時間（ネイティブ） |
|---|---|---|
| `roomCheckA` | 1 つの状態の表でバイトを持つ部屋のフレーム | 2〜3 秒 |
| `smallCheck` | バイトは 11 バイトの 1 つでルーチンのバイトでない、横の土管の入口の各基準は `v` を持つ | — |
| `ScreenStart.roomCheck` の最後の部分（パート b の確認） | `timeRows`（1 段、14,224 状態）の各状態がバイトを知る | 新しい歩きはない。段は確認がどのみち作るもの（プログラムとしての `ScreenStart.roomCheck`: 34 秒） |

出口の一覧にこのバイトがあっても、パート b の確認は同じ段で通ります。表を持つ段 44、状態 1,906、`soundCheck` 205 秒（前は 209 秒）。`Proof/AreaKeep.lean` は `gen-proofs` が書いたファイルから部屋と横の土管の名前を写し、`Proof.Rom` だけを読み込みます。`Proof/AreaJoin.lean` が道筋の名前で事実を述べます。写しは同じ項です（`rfl`）。

## 測ったこと: 2 つのバイトをどこで知るか

プログラムです。定理ではありません（`area-links-check`）。レベルの番号と足す音の長さは、縦の土管の基準の入口、出口、部屋の基準で 0 です。

| つなぎ | レベルの番号 | 足す音の長さ |
|---|---|---|
| 縦の土管の入口（`Entry`、`Rest`）、その出口、部屋の条件 | 知らない | 知らない（段の音の表のバイトで、始まりで知らない） |
| フレーム 0（`TitleStart` の近い状態、`EntryKeep.nearCheck`） | 知らない | 知る: 0 |
| 操作から縦の土管の入口までのフレーム（バイトを保つ `EntryKeep.keepCheck`、ガードで守る） | 保つ: 53,438 のうち失敗する歩き 0 | 失敗する歩き 4 |
| 縦の土管のフレーム（始まりでバイトを知り、出口で求める `zcheck`） | 保つ | 保つ |
| 出口からの時間の段（始まりにバイトを加えた写し） | 操作で知る | 操作で知る |
| 部屋のフレーム | 保つ（`roomCheckA`） | 保たない: 急ぎの音楽が 8 にする（回 12: エリア音楽のバッファが基準の値の表の 6 状態のうち 2 つが 8） |

この表は 15 回目より前のものです。15 回目から縦の土管の入口がレベルの番号を載せ（`Entry`）、16 回目からその出口も載せます（`exitNames`）。

レベルの番号が失敗したのはフレーム 0 だけでした。縦の土管の入口より前のフレームには、`upClean₁` のガードがこのバイトを守ることが要ります（パート b）。足す音の長さは 2 か所で失敗し、どちらもタイマーが原因です。イベントの音楽のコード（`LoadEventMusic`）は急ぎの音楽のときこのバイトを 8 にします。歩きはゲームタイマーを知らないので、急ぎの音楽が待ちにあるかどうかを知りません。

## 測ったこと: 横の土管の入口のゲームタイマー（`time₂`）

プログラムです。定理ではありません（`side-time-low FM2`、約 5 秒）。ムービーを部屋の最初の操作まで動かします（ムービーのフレーム 653 のあと。タイマーは 384、その制御タイマーは 24）。そこでタイマーを `0 0 v`、制御タイマーを `c` にし（`v` = 1 … 6、`c` = 0 … 24）、プレイヤーのルーチンを出るフレームまでムービーの入力で動かします。

| 部屋の最初の操作のタイマー | 結果 |
|---|---|
| 001、002、003、`c` ≤ 14 の 004 | 時間切れ: 25〜110 フレームのあとに死のルーチン、タイマー 000（90 の始まり） |
| `c` = 15 … 24 の 004、`c` = 0 … 14 の 005 | 111 フレームのあとに横の土管に入る。**タイマーは 000**（150 の始まりのうち 25） |
| `c` ≥ 15 の 005、006 | タイマー 001 か 002 で横の土管に入る |

だから `TimerOK(seq b₁)` から `TimerOK(seq a₂)` は出ません。部屋のフレームはタイマーを下げ、タイマーが 000 になってから時間切れまでの 24 フレームのうちに入れます。部屋は何フレームでも続きうるので、部屋の 1 フレームの条件ではタイマーを運べません。`a₂` でのタイマーには、タイマーを知るフレーム 0（`Route.Run.read₀`）からのフレームの数が要ります。歩きはタイマーを数として追わなければなりません（`24 · T + C` はポーズで終わらないフレームで高々 1 下がる）。抽象の機械はそれをしません。`DigitsMathRoutine` のステップは各桁を書き、桁への書き込みは `dg` を消します。

## 本物のフレームで

`area-real FM2 N R`（プログラム）: ムービーでは、横の土管のあとでバイトが最初に変わるまでの各フレーム、2 つの入口、部屋の最初の操作。`PipeTransitionAll.realEntries` の縦の土管への本物の入口から、それぞれ `N` 走り（土管のフレームで `R` フレームに 1 回乱数で Start）。部屋の最初の操作で測り、そのあと部屋の最初の操作からのムービーの入力で横の土管の入口まで。

| 走り | 縦の土管の入口 | 部屋の最初の操作 | 横の土管の入口 | バイトが 0 でない |
|---|---|---|---|---|
| ムービー | 1（フレーム 562） | 1（フレーム 653） | 1（フレーム 764） | なし: 電源からフレーム 1941 まで各フレームで 0。1-2 への切り替えのフレーム 1942 で変わる |
| `area-real FM2 10 7` | 本物の入口 13（`PipeTransitionAll.realEntries`） | 130（各 10 走り、土管のフレームで Start を乱数で） | 130（部屋の最初の操作からムービーの入力） | なし |

## 道筋で変わったこと

* `Run.chg : ChangesK … (restIdxA sy nmS m0)`: 横の土管の入口で 9 バイト（前は `restIdxR`、10 バイト）。`Run.chgK` は `Run.area₂` と `Run.rt₂` から 11 バイトの切り替えを出します。`Run.change₂`、`Run.start`、`Run.atCtl₀` は前と同じです。
* 14 回目には `Run` に新しいフィールド `area₁` がありました。15 回目からは定理 `Run.area₁` です。縦の土管の入口の条件がこのバイトを載せています（1-1-b-3-4-5）。
* `RoomChecks` に新しいフィールド `area : AreaKeep.Facts …` があります。道筋の非公開のファイル（5 回）と急ぎの音楽の非公開のファイル（1 回）で `area_facts` から作ります。16 回目からは部屋の歩きと小さい確認だけです（`room`、`small`）。土管のフレームと段はパート b のものです（`RoomChecks.pipe`、`RoomChecks.start`）。

仮定からなくなったもの: `entry₂` のレベルの番号。14 回目に加わったもの: `area₁`、縦の土管の入口でのレベルの番号。15 回目になくなりました。

## 仮定（Lean で証明していない）

* `area₁` はもう仮定ではありません（15 回目）。タイトルで Start を押したときの条件がこのバイトを求め（`title.boot`）、`upCleanU` のガードがそれを守り、`EntryKeep` の歩きが入口まで保ちます。そのぶん、この 2 つの仮定は 1 バイトずつ多く求めます。
* `chg.entry₂`: 横の土管の入口で 9 バイト: プレイヤーの高さ、画面のバッファ（5 バイト）、エリア音楽のバッファ、イベント音楽の待ち、足す音の長さ。 回 15 から、高さと画面のバッファの 5 バイトは入るフレームから出ます。入るフレームが小さいプレイヤーで、画面のバッファの制御が 0 で始まるときです（[1-1-d-2-5-4](d-2-5-4-EntryHeight-ja.md)、[1-1-d-2-5-5](d-2-5-5-EntryBuffer-ja.md)）。`chg.entry₂` は 3 バイトを求め、ほかの走りのために `Run` に 2 つのフィールド `height₂`、`buffer₂` がありました（どちらも今はありません: `height₂` は[部屋を通した大きさ](d-2-5-4-4-SizeKeep-ja.md)で、`buffer₂` は[コインのフレームはページ 0 で終わる](d-2-5-5-4-BufferPage-ja.md)でなくなりました）。
* `chg.time₂`: 横の土管の入口でゲームタイマーは 000 でない。

**ファイル.** `Theorems/AreaKeep.lean`、`Theorems/ScreenStart.lean`、`Theorems/PipeChangeEnd.lean`、`Theorems/Route.lean`。非公開の確認は `Proof/AreaKeep.lean` と `Proof/AreaJoin.lean`（`Main.lean` の `genAreaKeep`）。

**再現.**
```
.lake/build/bin/smbrta area-keep-check                 # 部屋の歩き、小さい確認、パート b の段のバイト、約 2 分
.lake/build/bin/smbrta area-links-check all            # 上の表（両方のバイト）、約 4 分
.lake/build/bin/smbrta side-time-low FM2               # 部屋の最初の操作でタイマーを下げる、約 5 秒
.lake/build/bin/smbrta area-real FM2 10 7              # 本物の走りでのバイト、約 20 秒
```
