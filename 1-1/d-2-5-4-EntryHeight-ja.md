[← Back](README-ja.md) | [English](d-2-5-4-EntryHeight.md) | [Japanese](d-2-5-4-EntryHeight-ja.md)

# 横の土管の入口の高さ

**主張.** 部屋のフレームが小さいプレイヤーで始まり、横の土管のルーチンで終わるなら、そのフレームは基準の入口の高さで終わります。ROM の 1 つの確認（部屋のフレームの歩き）で証明しました。そこで `Route.Run` は、入るフレームが小さいプレイヤーで始まる走りには、横の土管の入口の高さ（`Player_Y_Position`）を求めません。入るフレームがほかの大きさで始まる走りには、まだ求めます（新しいフィールド `height₂`）。`chg.entry₂` は 9 バイトでなく 8 バイトを求めます（1-1-d-2-5）。[画面のバッファ](d-2-5-5-EntryBuffer-ja.md) と合わせると 3 バイトです。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は入力 `i` での `m` の 1 フレーム、`tr(j)` はその `j` 命令目の機械です。`seq(n)` と `inp(n)` は、走りのフレーム `n` が始まるときの機械とその入力です。`rt(m)`、`y(m)`、`size(m)` はルーチンのバイト、高さ、プレイヤーの大きさです。`e_s` は横の土管のルーチン、`r` は部屋の基準の機械（小さいプレイヤー）、`y_e` は基準の入口の高さです。`b₁` は部屋の最初の操作、`a₂` は横の土管の入口です。`RoomCond`、`SiteOK` は [部屋での画面のページ](d-2-4-ScreenPage-ja.md) のものです。`K_T` は [部屋のブロックの地図](c-7-12-RoomMap-ja.md) のビットです: 部屋のバイト、ブロックバッファの各バイトで地図が 0 のビット、画面のバイト。

## 定理

```
K_Y             :=  K_T ∪ { size の全部のビット }
finY(B)         :=  B は rt ≠ e_s を知る   ∨   B は y = y_e を知る
WalkOK(fin)     :=  RoomCond(K) の始まりの状態からの歩きが通り、各フレームの終わりが fin を満たす

frame_end       :  WalkOK(fin),  RoomCond(K, m),  ∀ j, SiteOK(tr(j))        →   ∃ B,  fin(B) ∧ B は frame(m, i) を覆う
height_frame    :  WalkOK(finY),  RoomCond(K_Y, m),  ∀ j, SiteOK(tr(j)),  rt(frame(m, i)) = e_s      →   y(frame(m, i)) = y_e
height_of_rows  :  [b, a) での RoomMap.map_of_rows の仮定,  確認,  b ≤ k < a,
                   size(seq k) = size(r),   rt(frame(seq k, inp k)) = e_s           →   y(frame(seq k, inp k)) = y_e

Run.height₂     :  size(seq(a₂ − 1)) = size(r)   ∨   y(seq a₂) = y_e                 （フィールド、新しい）
Run.y₂          :  y(seq a₂) = y_e                                                    （定理）
entryAt_of_y    :  m[y] = y_e  ∧  EntryAt(R₈, m)   →   EntryAt(R₉, m)
```

`R₉` は `restIdxA` の 9 バイト、`R₈ := R₉ \ {y}` です（`restIdxY`）。`EntryAt` は [横の土管の入口のルーチン](d-2-5-2-EntryRoutine-ja.md) のものです。

**`Run.y₂`.** `b₁ < a₂` です（`Run.b₁_lt_a₂`）。だからフレーム `a₂ − 1` は部屋のフレームで、横の土管のルーチンで終わります（`Run.rt₂`）。`size(seq(a₂ − 1)) = size(r)` なら `height_of_rows` が高さを出します。そうでなければ `height₂` が出します。

Lean: `Theorems/EntryHeight.lean`（`HP`、`bitSet`、`top2`、`top1`、`topY`、`lowA`、`zoneY`、`preY`、`stepY`、`finY`、`walkY`、`mix64`、`keyY`、`normY`、`Opts`、`optsY`、`putY`、`routeY`、`runY`、`searchY`、`searchOf`、`cfgOf`、`walkCheckY`、`cov_top2`、`cov_top1`、`cov_topY`、`cov_lowA`、`cov_zoneY`、`cov_preY`、`s_stepY`、`LiveY`、`cover_liveY`、`live_stepY`、`frame_of_walkY`、`WalkOK`、`walkOK_of_check`、`frame_end`、`height_frame`、`sizeI`、`heightI`、`hpOf`、`aidsY`、`knownY`、`heightCheck`、`refsCheck`、`Facts`、`factsOf`、`height_of_rows`）、`Theorems/Route.lean`（`restIdxY`、`RoomChecks.height`、`Run.height₂`、`Run.y₂`、`entryAt_of_y`、`Run.chgK`）、非公開の `Proof/EntryHeight.lean`（`entry_height_walk`、`entry_height_refs`、`height_facts`）。公開のファイルにゲームのデータはありません。`height_frame` と `height_of_rows` が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

## しくみ

**高さが段ちょうどである理由.** 横の土管のコード（`ChkPBtm`）は、プレイヤーの状態が「立っている」ことを求めます。当たり判定のルーチン（`PlayerBGCollision`）は、まず「立っている」を「落ちている」にします。状態を「立っている」に戻す場所は 1 か所だけです（`InitSteP`）。コードがそこへ来るのは、着地（`LandPlyr`）のあとか、ジャンプ台が動いているときです。着地はまず高さを段に切り下げます。ジャンプ台が動いていないことは部屋の条件が知っています。だから入るフレームでは、横の判定のときの高さは段ちょうどです。

**歩き.** [部屋のブロックの地図](c-7-12-RoomMap-ja.md) の部屋のフレームの歩き（`RoomMap.stepT`）に、分け方を 4 つ足したものです。どれも仮定が要りません。どの機械も覆います。

* 足の判定が高さを読むところ: 高さの上のビットを 6 つに分けます（`0xxxxxxx`、`10xxxxxx`、`1100xxxx`、`1101xxxx`、`1110xxxx`、`1111xxxx`）。足の判定は高さを画面の下の近くの値と比べます。抽象の機械が結果を知らないのは 1 つだけです。だからその値以上の部分は着地に来ません。
* 着地が高さを書いたあと: 高さの各値（13 段）。
* ブロックバッファの番地を作るところ（高さを知っているとき）: A レジスタの下 5 ビット（列とバッファ）。これで読み出しのポインタが分かります。
* ブロックバッファのルーチンがタイルを保存したあと: タイルの各値。

**読み出し.** ポインタと段が分かっているとき、歩きはブロックバッファのルーチンの読み出しで機械そのもののステップを使います（`stepY`）。ブロックバッファのバイトを読みます。部屋の条件は、このバイトのうち地図で 0 のビットを知っています。ほかのところでは、前と同じく読み出しは表のタイルを返します（`SiteOK`）。

**高さが 1 つだけである理由.** 地図で横の土管のタイルのビットを持つ場所は 1 つだけです。口の下のタイルです。小さいプレイヤーの横の 2 つの読み出しは同じ段です。だからその場所を読む高さは 1 つだけです。歩きはこれを確かめます: どのフレームの終わりも、ルーチンが横の土管のものでないと知るか、高さを知っていて `y_e` に等しいかです。

**探索（証明の一部ではない）.** キーには高さ、プレイヤーの状態、読み出しのポインタが入ります。状態がキーにないと、「跳んでいる」と「落ちている」の状態が合わさり、合わせた状態は「立っている」も許します。当たり判定のルーチンの足す数の番号は忘れません（`aidsY`）。当たり判定のルーチンのあとでは、ルーチンが横の土管のものでなければ高さを忘れます。

探索について、途中で 2 つのことが分かりました。ハッシュ表はキーの下 64 ビットだけを読みます。部屋のキーの下 64 ビットは少しの値しか取りません（スタックと 2 バイト）。そのようなキーでの 180 万ステップの探索は 110〜206 秒かかりました。キーの下に混ぜた 64 ビットを置くと（`mix64`）、120 万ステップの探索は 7 秒です。部屋のほかの歩きも同じキーを使います（`ScreenPage.Aids.key`）。もう 1 つ、部屋の探索の待ち行列はキーを 2²⁰⁰ で割った余りで並べます（`SearchS.put`）。キーが長いと 2 つの状態が同じ場所を取り、1 つがなくなります。この歩きは自分の待ち行列を持ちます（`putY`）。

**大きさ.** 1,230,581 ステップ、49,455 分岐、失敗 0、199,714 状態。プログラムで: 探索 6.8 秒、確認 約 20 秒。`Proof/EntryHeight.lean` は、この確認だけで 34 秒、[画面のバッファ](d-2-5-5-EntryBuffer-ja.md) の確認と合わせて、ほかのビルドが動いているときに 69 秒で作られました。数秒より長いです。

## 測ったこと（定理ではない）

フレームの始まりでほかの大きさにした歩き（`entry-height-check FM2 N walkall`）:

| フレームの始まりの大きさ | ステップ | 失敗 | 横の土管のルーチンで終わるフレームの終わり | その高さ |
|---|---|---|---|---|
| 基準のもの（小さい） | 1,230,581 | 0 | 8 | 176 px |
| 大きい | 2,300,695 | 4 | 24 | 176 px と 192 px（8 個） |
| 知らない | 2,432,097 | 4 | 24 | 176 px と 192 px（8 個） |

**大きいプレイヤー: 証明できた部分.** `RoomBlocks.Solid` で床を使えますが、高さ全体の証明は未完です。`EntrySolid.cond` は、既存の部屋の条件と `Solid` から、地図のコイン以外の各バイトをすべて知る条件を与えます。コインには元の 0 のビットを残します。基準との一致は、非公開の `Proof/EntrySolidFacts.lean` の `entry_solid_refs` で確認します。走りの仮定は増やしません。

床を知る歩きにも抽象的な失敗が 62 個あり、192 px で入る終端が 8 個あります。実機の 1 フレームの試行でも、床がありながら 192 px で入る候補がありました。ただし、それらはすべて `SiteOK` の頭の読み出しの条件に反します。全仮定を満たす反例ではありません。「床だけで防げる」という前の説明は不十分でした。

試作した歩きでは、頭の読み出し位置、横位置の 64 分割、`SiteOK` による絞り込み、アドレスが分かるコインの消去を扱いました。最大の有限探索は 1,500,001 状態で上限に達し、206,279 状態とすべてのフレーム終端が未処理でした。高さは証明していません。この重い変更は本来の歩きには残していません。`height₂` はそのままです。頭と横の読み出しの位置関係が残る問題です。

## 本物のフレームで

プログラムです（`entry-height-check FM2 400 real`、約 3 分）。

| 走り | フレーム | 入った数 | フレームは `RoomCond(K_T)` で始まる | 基準の大きさで | どの命令も `SiteOK` | 入口の高さ | `height₂`、`buffer₂`、`entry₂` が成り立つ |
|---|---|---|---|---|---|---|---|
| ムービーの入るフレーム（ムービーのフレーム 763） | 1 | 1 | 1 | 1 | 1 | 176 px | 1 |
| ムービーの入るフレームから 1 フレーム、小さい。高さ（112 から 207 px）、上下の状態、上下の速さを書き換える | 1,440 | 55 | | | | 176 px | |
| 同じ、大きい | 1,440 | 55 | | | | 176 px | |
| 部屋のムービーのフレームから自分の入力、小さい（400 走り） | 164,375 | 142 | 142 | 142 | 142 | 176 px | 142 |
| 同じ、大きい | 161,042 | 151 | 151 | 0 | 151 | 176 px | 151 |

大きいプレイヤーでは `height₂` の左側は偽で、右側が成り立ちます。

## ほかのパートから使うもの

* パート c: `RoomMap.cond_of_rows`（各フレームの始まりで、地図のビットを持つ部屋の条件。確認は `map_facts`、`map_start`）、ステップ `RoomMap.stepT` と `RoomMap.s_stepT`。`Run.rt₂` を通して、フィールド `room.enters`、定理 `Run.roomEnter`、歩き `SideEntryEnd`、`SideEntryRest`。
* パート b: 部屋の最初の操作での最初の切り替えの段（`ChangesK.run₁`、`inRowsT`）、`ctl₁`、`ctlFirst₁`、`Run.entry₁`。
* 循環はありません。どれも `entry₂` を使いません。

## 道筋で変わったこと

* `Run.chg : ChangesK … (restIdxB sy nmS m0)`（3 バイト。`restIdxY` は高さを除いた 8 バイト）。`Run.chgK` は `Run.buf₂`、`Run.y₂`、`Run.area₂`、`Run.rt₂` から 11 バイトの切り替えを出します。
* `Run` に新しいフィールド `height₂` があります。
* `RoomChecks` に新しいフィールド `height : EntryHeight.Facts …` があります。道筋の非公開のファイル（5 回）と急ぎの音楽の非公開のファイル（1 回）で `height_facts` から作ります。

仮定からなくなったもの: 入るフレームが小さいプレイヤーで始まる走りでの、`entry₂` の高さ。加わったもの: `height₂`。前の仮定から出ます。

## 仮定（Lean で証明していない）

* `height₂`: 入るフレームは小さいプレイヤーで始まる、または入口の高さは基準の入口のもの。
* 部屋の各命令の `SiteOK`（`chg.roomSites`）。前と同じです。

**ファイル.** `Theorems/EntryHeight.lean`、`Theorems/Route.lean`。非公開の確認は `Proof/EntryHeight.lean`（`Main.lean` の `genEntryHeight`）。

**再現.**
```
.lake/build/bin/smbrta entry-height-check FM2 10 walk       # 2 つの歩きの探索と確認、約 40 秒
.lake/build/bin/smbrta entry-height-check FM2 10 walkall    # 大きいプレイヤーと、大きさを知らない場合も、約 2 分
.lake/build/bin/smbrta entry-height-check FM2 400 real      # 本物のフレームの表、約 3 分
```
