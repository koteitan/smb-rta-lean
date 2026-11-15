[← Back](README-ja.md) | [English](d-2-5-3-AreaKeep.md) | [Japanese](d-2-5-3-AreaKeep-ja.md)

# 縦の土管から横の土管までのレベルの番号

**主張.** 縦の土管の入口でレベルの番号（`AreaNumber`）が基準の入口の値なら、横の土管の入口でもその値です。ROM の 3 つの歩きで証明しました。そこで `Route.Run` は横の土管の入口で 10 バイトでなく 9 バイトを求め（`chg.entry₂`、1-1-d-2-5）、縦の土管の入口で新しく 1 バイトを求めます（`area₁`）。仮定は横の土管の入口から縦の土管の入口へ移りました。なくなってはいません。

このページは、この回のほかの 2 つの候補について測ったことも書きます。足す音の長さ（`NoteLengthTblAdder`）と、横の土管の入口でのゲームタイマー（`chg.time₂`）です。どちらも部屋のフレームを通りません。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は入力 `i` での `m` の 1 フレーム、`trₙ(j)` はフレーム `n` の `j` 命令目の機械です。`seq(n)` はフレーム `n` が始まるときの機械です。`a₁`、`b₁`、`a₂` は縦の土管の入口、部屋の最初の操作、横の土管の入口です（`Route.Base`）。`i` はレベルの番号の番地、`e` は縦の土管の基準の入口、`v := e[i]` です。`S[i ↦ v]` は、`i` も値 `v` で知る抽象の状態 `S` です。`rt(m)` はルーチンのバイト、`r` は部屋の基準の機械です。

## 定理

`startsP` と `baseK` は縦の土管のフレームの歩きの始まりの状態と出口の状態です（[部屋への切り替え](b-3-2-PipeChangeEnd-ja.md)）。`rowsKc` は出口から部屋の最初の操作までの表を持つ段です（[音のバイトを表で運ぶ](b-3-7-1-SoundRows-ja.md)）。`DuringV`、`InRowsK`、`QuietP`、`SongAt`、`TimerOK` はパート b のものです。

```
startsA  :=  { S[i ↦ v] : S ∈ startsP }           baseA  :=  { S[i ↦ v] : S ∈ baseK }
DuringA(m)  :=  m は startsA からの土管のフレームの歩きに入る
InRowsA(m)  :=  m は baseA からの表を持つ段に入る

PipeRunK.areaB :  a から b までのパート b の切り替えの走り,  b は a のあとの最初の操作,  seq(a)[i] = v   →   seq(b)[i] = v
area_run       :  Room(seq c),  seq(c)[i] = v,
                  ∀ n ∈ [c, e):  (∀ j, SiteOK(trₙ(j))) ∧ rt(seq n) = rt(r),     rt(seq e) ≠ rt(r)
                  →  seq(e)[i] = v

Run.area₁       :  seq(a₁)[i] = v                                         （フィールド、新しい）
Run.area₂       :  seq(a₂)[i] = v                                         （定理）
entryAt_of_area :  m[i] = v  ∧  EntryAt(R₉, m)  →  EntryAt(R₁₀, m)
chg.entry₂      :  EntryAt(R₉, seq a₂)                                    （9 バイト。前は R₁₀）
```

`R₁₀` は `restIdxR` の 10 バイト、`R₉ := R₁₀ \ {i}` です（`restIdxA`）。`EntryAt` は [横の土管の入口のルーチン](d-2-5-2-EntryRoutine-ja.md) のものです。

**`PipeRunK.areaB`** は切り替えのフレームについての帰納法です。`n = a + k ≤ b` で次を保ちます。

```
( DuringV(seq n) ∧ DuringA(seq n) )  ∨  ( InRowsK(seq n) ∧ InRowsA(seq n) )
```

各側の左半分はパート b の歩きから出ます（`EndStatement.pauseStep`、`rowsK`、`zeroK`）。右半分はバイトを持つ歩きから出ます。土管の中では、2 つの歩きはフレームが土管を出るかどうかで一致しなければなりません。`DuringA` の状態は土管のルーチンにあります（始まりの状態の確認 `pipeOK`）。出口の機械は土管のルーチンにありません（出口のタスクはゲームコアでない）。出口では `QuietP`、`SongAt`、`TimerOK` がパート b の走りから出て、機械を `baseA` からの最初の段に入れます（`rowsA_of_exit`、`PipeChangeEnd.inRowsK_of_exit` と同じ）。段の中では `b` より前に `left` は 0 になりません。パート b の段は `left` が 0 のところで操作でき、`b` は最初の操作だからです。`b` で機械は `baseA` からの段にあり、各段の各状態はバイトを値 `v` で知ります（`knowsRows`）。

**`area_run`** は 1 つの状態の表 `[(i, v)]` での `RoomPause.pause_run` です。音のルーチンの区間では、歩きは表からバイトを知ります。区間の外では、バイトを書くかもしれないステップで歩きは失敗します。

**`Run.area₂`.** `area₁`、最初の切り替えのパート b の走り（`ChangesK.run₁`）、`PipeRunK.areaB` が `b₁` でのバイトを出します。`b₁` から `a₂` までの `area_run`（`b₁` での部屋の条件、`roomSites`、`roomStay`、`a₂` でほかのルーチンになることに `Run.rt₂`）が `a₂` でのバイトを出します。

Lean: `Theorems/AreaKeep.lean`（`areaI`、`setA`、`startsA`、`baseA`、`cfgRa`、`cfgOa`、`pipeCheckA`、`startsKA`、`rowsA`、`InRowsA`、`knowsRows`、`rowsCheckA`、`regA`、`cfgA`、`roomCheckA`、`smallCheck`、`zok_of_check`、`sim_setA`、`duringA_of_entry`、`inPipe_of_A`、`not_inPipe_of_exit`、`rowsA_of_exit`、`rowsA_step`、`area_of_rowsA`、`PipeRunK.areaB`、`roomOK_of_check`、`area_run`、`Facts`、`factsOf`、`small_parts`）、`Theorems/Route.lean`（`restIdxA`、`RoomChecks.area`、`Run.area₁`、`Run.area₂`、`entryAt_of_area`、`Run.chgK`）、非公開の `Proof/AreaKeep.lean`（`area_pipe`、`area_rows`、`area_room`、`area_small`、`area_factsA`）と `Proof/AreaJoin.lean`（`area_facts`）。公開のファイルにゲームのデータはありません。

## 確認

| 確認 | 歩くもの | 時間（ネイティブ） |
|---|---|---|
| `pipeCheckA` | `startsA` からの縦の土管のフレーム（パート b の歩き `zcheck`）。`baseA` で終わる | 15〜18 秒 |
| `rowsCheckA` | `baseA` からの表を持つ段: 44 段、1,906 状態。`chainS` と、各状態がバイトを知ること | 120〜136 秒 |
| `roomCheckA` | 1 つの状態の表でバイトを持つ部屋のフレーム | 2.3〜2.5 秒 |
| `smallCheck` | バイトは 11 バイトの 1 つでルーチンのバイトでない、出口のタスクはゲームコアでない、横の土管の入口の各基準は `v` を持つ | — |

段の確認は約 2 分かかります。パート b の段のフレームごとの確認（`soundCheck`、同じ 44 段と 1,906 状態で約 200 秒）を、バイトを持つ段でするからです。パート b の長い確認を待たないように、`Proof/AreaKeep.lean` は `gen-proofs` が書いたファイルから名前と切り替えのデータを写し、`Proof.Rom` だけを読み込みます。`Proof/AreaJoin.lean` が道筋の名前とデータで事実を述べます。写しは同じ項です（`rfl`、0.2 秒）。

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

レベルの番号が失敗するのはフレーム 0 だけです。縦の土管の入口より前のフレームには、`upClean₁` のガードがこのバイトを守ることが要ります（パート b）。足す音の長さは 2 か所で失敗し、どちらもタイマーが原因です。イベントの音楽のコード（`LoadEventMusic`）は急ぎの音楽のときこのバイトを 8 にします。歩きはゲームタイマーを知らないので、急ぎの音楽が待ちにあるかどうかを知りません。

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
* `Run` に新しいフィールド `area₁` があります。
* `RoomChecks` に新しいフィールド `area : AreaKeep.Facts …` があります。道筋の非公開のファイル（5 回）と急ぎの音楽の非公開のファイル（1 回）で `area_facts` から作ります。

仮定からなくなったもの: `entry₂` のレベルの番号。加わったもの: `area₁`、縦の土管の入口でのレベルの番号。

## 仮定（Lean で証明していない）

* `area₁`: 縦の土管の入口でレベルの番号は基準のもの。フレーム 0 はこれを知りません（`TitleStart`）。操作から入口までのフレームは、`upClean₁` のガードが守れば保ちます（測った）。
* `chg.entry₂`: 横の土管の入口で 9 バイト: プレイヤーの高さ、画面のバッファ（5 バイト）、エリア音楽のバッファ、イベント音楽の待ち、足す音の長さ。
* `chg.time₂`: 横の土管の入口でゲームタイマーは 000 でない。

**ファイル.** `Theorems/AreaKeep.lean`、`Theorems/Route.lean`。非公開の確認は `Proof/AreaKeep.lean` と `Proof/AreaJoin.lean`（`Main.lean` の `genAreaKeep`）。

**再現.**
```
.lake/build/bin/smbrta area-keep-check                 # 4 つの確認、約 3 分 30 秒
.lake/build/bin/smbrta area-links-check all            # 上の表（両方のバイト）、約 4 分
.lake/build/bin/smbrta side-time-low FM2               # 部屋の最初の操作でタイマーを下げる、約 5 秒
.lake/build/bin/smbrta area-real FM2 10 7              # 本物の走りでのバイト、約 20 秒
```
