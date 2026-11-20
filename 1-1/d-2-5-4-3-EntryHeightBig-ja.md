[← Back](README-ja.md) | [English](d-2-5-4-3-EntryHeightBig.md) | [Japanese](d-2-5-4-3-EntryHeightBig-ja.md)

# 大きいプレイヤーの横の土管の入口の高さ

**主張.** 部屋のフレームが大きいプレイヤー（大きさのバイトが 0）で始まり、横の土管のルーチンで終わるなら、そのフレームは基準の入口の高さ（176 px）で終わります。ROM の 1 つの確認（部屋のフレームの歩き）で証明しました。そこで `Route.Run` のフィールド `height₂` は狭くなりました。入るフレームが大きいプレイヤーで始まる走りには、もう高さを求めません。そのフレームの始まりの大きさのバイトが基準（小さい）でも 0 でもないときは、まだ求めます。

[高さ](d-2-5-4-EntryHeight-ja.md) の古い歩きは、大きいプレイヤーで 192 px のフレームの終わりが 8 個ありました。その抽象機械は頭を読むときに高さを知らないので、頭がどのマスを読むかを知りません。新しい歩きは、192 px で終わりうるフレームでそれを知ります。そのフレームで頭は土管か床のマスを読みます。`SiteOK` はそこで 0 かコインしか許しません。だから 192 px で終わるフレームはありません。

`m[i]` は `m` の RAM のバイト `i`、`frame(m, i)` は入力 `i` での `m` の 1 フレーム、`tr(j)` はその `j` 命令目の機械、`step(m)` は 1 命令です。`rt`、`y`、`x`、`pg`、`size` はルーチンのバイト、高さ、横の位置、ページ、プレイヤーの大きさです。`e_s` は横の土管のルーチン、`y_e` は基準の入口の高さ（176 px）、`d_L` は着地の深さ（ROM の `LandDepth`、5）です。`r` は部屋の基準の機械（小さいプレイヤー）、`r_B` はその大きさのバイトを 0 にした機械です。`K_T` は [部屋のブロックの地図](c-7-12-RoomMap-ja.md) のビット、`K_Y := K_T ∪ { size の全部のビット }` です。`map` は部屋のブロックの地図、`coins` はそのコインのタイルです。

## 定理

```
band(y)          :=  y_e + 16 ≤ y < y_e + 16 + d_L                       (192 ≤ y < 197)
Solid(m)         :=  ブロックバッファの各 d で、 map[d] ∉ coins  →  m[d] = map[d]
finY(B)          :=  B は rt ≠ e_s を知る   ∨   B は y = y_e を知る
WalkOKB          :=  RoomCond(r_B, K_Y) の始めの状態からの新しい歩きが通り、フレームの終わりはどれも finY を満たす

adc0_a           :  pc(m) の命令が ADC #0,  carry(m) = 0     →   a(step(m)) = a(m)
s_stepB          :  A が m を覆う,  SiteOK(m),  Solid(m)     →   stepB(A) のある次の状態が step(m) を覆う
height_frameB    :  WalkOKB,  RoomCond(r_B, K_Y, m),  ∀ j, SiteOK(tr(j)),  フレームの終わりの前の ∀ j, Solid(tr(j)),  rt(frame(m, i)) = e_s
                       →   y(frame(m, i)) = y_e
height_of_rowsB  :  [b, a) で RoomMap.map_of_rows の仮定,  確認,  b ≤ k < a,  size(seq k) = 0,  rt(frame(seq k, inp k)) = e_s
                       →   y(frame(seq k, inp k)) = y_e

Run.height₂      :  size(seq(a₂ − 1)) = size(r)   ∨   size(seq(a₂ − 1)) = 0   ∨   y(seq a₂) = y_e        （フィールド、狭めた）
Run.y₂           :  y(seq a₂) = y_e                                                                   （定理）
```

**`Run.y₂`.** フレーム `a₂ − 1` は部屋のフレームで、横の土管のルーチンで終わります（`Run.b₁_lt_a₂`、`Run.rt₂`）。小さいプレイヤーで始まれば `EntryHeight.height_of_rows` が高さを与えます。大きさ 0 で始まれば `height_of_rowsB` が与えます。各命令の `Solid` は `RoomBlocks.blocks_run_trace` から来ます。それ以外は `height₂` が与えます。

Lean: `Theorems/EntryHeightBig.lean`（`HB`、`meets`、`band`、`bits`、`inBand`、`zoneB`、`preB`、`refineA`、`ptrLo`、`ptrHi`、`readAd`、`readI`、`solidAt`、`stepB`、`walkB`、`keyB`、`normB`、`optsB`、`runB`、`searchB`、`searchOfB`、`cfgOfB`、`adcOK`、`walkCheckB`、`cov_band`、`bits_ok`、`cov_zoneB`、`cov_preB`、`op_69`、`adc0_a`、`AdcOK`、`adcOK_spec`、`s_stepB`、`LiveB`、`cover_liveB`、`PlB`、`live_stepB`、`frame_of_walkB`、`WalkOKB`、`walkOKB_of_check`、`frame_endB`、`height_frameB`、`hbOf`、`hbOf_H`、`hbOf_coins`、`hbOf_map`、`hpOf_P`、`refB`、`checkB`、`cond_ref`、`Facts`、`factsOf`、`height_of_rowsB`）、`Theorems/Route.lean`（`RoomChecks.height`、`Run.height₂`、`Run.y₂`）、非公開の `Proof/EntryHeight.lean`（`entry_height_big`、`height_facts`）。公開のファイルにゲームのデータはありません。

## しくみ

歩きは [高さ](d-2-5-4-EntryHeight-ja.md) の歩き（`EntryHeight.preY`、`EntryHeight.stepY`）に、分け方を 2 つと、ステップを 2 種類足したものです。どの分け方もすべての機械を覆います（`cov_zoneB`）。仮定はありません。

* **帯.** 衝突のルーチンが最初に高さを読むところ（頭の確認の比較の前）で、高さを上のビットから 1 つずつ分けます。その片が `band` の値をまだ持ちうるあいだだけ分けます（`band`）。片は 12 個です。帯の 5 個の片では高さがわかります。ほかの片ではわかりませんが、192 px の行には着地できません。
* **位置.** 頭のためのブロックバッファのルーチンの呼び出しで、高さがわかっていて帯にあるとき、横の位置（256 個の値）とページのビット 0 で分けます。すると同じ片で、頭のマスと横の読みのマスがわかります。
* **ページの `ADC #0`.** ブロックバッファのルーチンは、`ADC #0` でページにキャリーを足します。抽象的な `ADC` は、バイトがわからないと何も知りません。キャリーが 0 とわかっているとき、新しいステップはアキュムレータにページを残します（`refineA`、`adc0_a`）。だから頭の読みと横の読みで、ブロックバッファの半分が同じです。
* **場所がわかる読み.** ブロックバッファのルーチンの読みで、ポインタと Y がわかり、地図でコインでないブロックバッファのバイトを読むとき、ステップは地図のバイトを読みます（その命令の `Solid`）。`SiteOK` がそこでそのバイトを許さないなら、その片に機械はありません（`stepB`、空のリスト）。頭の読みは 0 かコインしか読みません（`SiteOK.read`）。床と土管はどちらでもありません。

**探索（証明の一部ではない）.** キーに位置とページを入れます。そうしないと 512 個の片が、衝突のルーチンが戻る前にまたつながります。戻るところで忘れます（`normB`）。キューはキーの下の 512 ビットしか持たないので、位置とページはビット 512 より下に置きます。

**大きさ.** 8,326,333 ステップ、264,339 の分かれ、失敗 0、状態 1,267,661。フレームの終わり 272 個、そのうち横の土管のルーチン 64 個、すべて 176 px。プログラムで探索 44 秒、確認 324 秒。

## 途中で測ったこと（定理ではない）

* 大きさを知らない歩き（`RoomMap.knownT`、衝突のルーチンの始めで大きさを分ける）は通りませんでした。11,770,114 ステップ、失敗 34、192 px の終わり 68 個。頭の確認が大きさを読む前に、大きさがまたつながりました。大きさをキーに入れると探索は 11 分を超え、止めました。だから `height₂` は大きさのバイトのほかの値を残します。
* 頭の呼び出しで分けるだけでは足りません。頭の確認は呼び出しの前に高さを比べます。高さがわからないと、歩きは頭の読みを飛ばします。だから帯は、その比較の前に分けます。
* 失敗 0 の最初の測定は誤りでした。キーが位置をビット 512 より上に置き、キューが状態をなくしました。使っていません。

## 本物のフレームでの確認

[高さ](d-2-5-4-EntryHeight-ja.md) を見てください。`entry-height-check FM2 5 real` と `50 real` は、TAS と自分のでたらめな入力の走り（小さいと大きい）で `height₂` を確かめます。新しいフィールドは古いものより弱いので、古いフィールドを満たす走りは新しいものも満たします。TAS の `route-check` も通ります。

## ほかの部分から使うもの

* パート c: `RoomMap.cond_of_rows`、`RoomMap.s_stepT`（`EntryHeight.s_stepY` を通して）、`RoomBlocks.blocks_run_trace` とその確認 `BChecks`、`rowsCheckR`（部屋のフレームの各命令の地図のバイト）、`RoomBlocks.readAddr_eq`、`RoomBlocks.readVal_eq`、`RoomBlocks.tick_a`。
* パート d: `EntryHeight`（歩きの片とステップ、`refsCheck`）。
* パート b: 部屋の最初の操作での最初の切り替えの行（`ChangesK.run₁`、`inRowsT`）、`ctl₁`、`ctlFirst₁`、`Run.entry₁`。`Run.y₂` を通して、前と同じです。
* 循環なし: `RoomBlocks.blocks_run_trace` は `roomSites`、`roomStay`、`ctl₁` と最初の切り替えの行を使います。どれも `height₂` も `entry₂` も使いません。

## ルートで変わったこと

* `Run.height₂` に真ん中の選択肢 `size(seq(a₂ − 1)) = 0` が増えました。古いフィールドから新しいものが出ます。
* `RoomChecks.height` は `EntryHeightBig.Facts` になりました。`EntryHeight` の事実、確認 `checkB`、`RoomBlocks` の確認です。

仮定から除いたもの: 入るフレームが大きいプレイヤーで始まる走りの、横の土管の入口の高さ。足したもの: なし。

## 仮定（Lean で証明していない）

* 入るフレームの始まりで大きさのバイトがほかの値（基準でも 0 でもない）のときの `height₂`。
* 部屋の各命令の `SiteOK`（`chg.roomSites`）。前と同じです。

## 時間

`Proof/EntryHeight.lean` は `checkB` もネイティブに走らせます。ラウンド 21 の全体の `prove.py` で 355 秒かかりました（前は小さいプレイヤーの歩きだけで約 45 秒）。プログラムでは `checkB` だけで 324 秒です（探索 44 秒、その後に表の上の歩き）。数秒よりずっと長いです。

**ファイル.** `Theorems/EntryHeightBig.lean`、`Theorems/Route.lean`。非公開の確認は `Proof/EntryHeight.lean`（`Main.lean` の `genEntryHeight`）です。プログラム `entry-head-diag check 0` が探索と確認を走らせます。
