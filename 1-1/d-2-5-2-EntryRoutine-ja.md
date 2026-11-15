[← Back](README-ja.md) | [English](d-2-5-2-EntryRoutine.md) | [Japanese](d-2-5-2-EntryRoutine-ja.md)

# 横の土管の入口のルーチン

**主張.** 横の土管の入口（フレーム `a₂`）で、ルーチンのバイトは横の土管のものです。部屋の入るフレームから証明しました。そこで `Route.Run` は入口で 11 バイトでなく 10 バイトを求めます（`chg.entry₂`、1-1-d-2-5）。新しい小さなフィールドが 1 つあります。`a₂` の探索は部屋の最初の操作から少なくとも 1 フレーム先まで見ます（`dR_pos : 1 ≤ dR`）。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は入力 `i` での `m` の 1 フレーム、`tr(j)` はその `j` 命令目の機械です。`seq(n)`、`inp(n)` は走りのフレーム `n` が始まるときの機械とその入力です。`rt(m)` はルーチンのバイト、`e_s` は横の土管のルーチン、`r` は部屋の基準の機械です。`b₁` は部屋の最初の操作です。`a₂ = firstWith(p, b₁, dR)` は `b₁` から `dR` フレーム以内で最初の `p(n) := rt(seq n) ≠ rt(r)` のフレームです。`R₁₁` は `RoomMusic.restIdxM` の 11 バイト、`R₁₀ := R₁₁ \ {rt}` です。`V` は入口の基準です。

## 定理

```
EntryAt(L, m)   :=  ∃ (v, X) ∈ V,  ∀ i ∈ X,  i ∈ L  →  m[i] = v[i]

rest_rt        :  RestOK,  RoomCond(m),  ∀ j, SiteOK(tr(j)),
                  ∀ j, (∀ k ≤ j, rt(tr(k)) ≠ e_s) → HypW(tr(j)),
                  ∃ n, rt(tr(n)) ≠ e_s ∧ rt(tr(n + 1)) = e_s
                  →  rt(frame(m, i)) = e_s
rt_of_rows     :  [b, a) で RoomMap.map_of_rows の仮定,  確認,  b ≤ k < a,  Enters(seq k, inp k)
                  →  rt(frame(seq k, inp k)) = e_s

Run.b₁_lt_a₂   :  1 ≤ dR  →  b₁ < a₂
Run.rt₂        :  rt(seq a₂) = e_s
entryAt_of_rt  :  rt(m) = e_s  ∧  EntryAt(R₁₀, m)  →  EntryAt(R₁₁, m)
Run.chgK       :  EntryAt(R₁₁, seq a₂) を持つ切り替え。chg と Run.rt₂ から
```

**`rest_rt`** は `SideEntryRest.rest_end` の帰納法で、結論が違います。`SideEntryRest` の歩きは各ステップで、ルーチンのバイトが一度 `e_s` になったら `e_s` のままであることを求めます（`okT`）。`rest_end` は証明の中でこれを示して位置を結論します。`rest_rt` はフレームの終わりのルーチンのバイトを結論します。**`rt_of_rows`** は `SideEntryRest.mouth_of_rows` と同じように、入るフレームの 2 つの歩きをつなぎます。`SideEntryEnd` の歩きが最初の書き込みまで `HypW` を出し、`rest_rt` がルーチンをフレームの終わりまで運びます。

**`Run.b₁_lt_a₂`.** `rt(seq b₁) = rt(r)` です（最初の操作での部屋の条件、`ChangesK.roomAt`）。だから `p(b₁)` は偽です。`dR = d + 1` なら `firstWith(p, b₁, d + 1) = firstWith(p, b₁ + 1, d) ≥ b₁ + 1` です。

**`Run.rt₂`.** `Run.roomEnter`（パート c）は、部屋の入るフレームを走りのフレーム `k`、`b₁ ≤ k < a₂` として出します。このフレームは `e_s` を書きます（`room.enters`）。`rt_of_rows` から `rt(seq(k + 1)) = e_s` です。`b₁ ≤ n < a₂` の各フレーム `n` は `rt(seq n) = rt(r) ≠ e_s` です（`ChangesBase.roomStay`、`RoomFacts.ne`）。だから `k + 1 < a₂` は偽で、`a₂ = k + 1` です。

**`entryAt_of_rt`.** 各基準はルーチンのバイトを値 `e_s` で挙げます（`RoomChecks.rt`）。`i = rt` の値は `rt(m) = e_s` から出ます。`R₁₁` のほかのバイトは `R₁₀` にあります。

Lean: `Theorems/EntryRoutine.lean`（`rest_rt`、`rt_of_rows`）、`Theorems/Route.lean`（`EntryAt`、`restIdxR`、`ChangesBase` と `ChangesK` の引数 `L`、`entryAt_of_rt`、`Run.dR_pos`、`Run.b₁_lt_a₂`、`Run.rt₂`、`Run.chgK`、`RoomChecks` の新しいフィールド）。ROM の新しい確認はありません。歩きはパート c のもので、その非公開の確認 `map_facts`、`map_start`、`map_startF`、`side_entry_end_check`、`side_rest_check` を使います。

## ほかのパートから使うもの

* パート c: フィールド `room.enters`（部屋のフレーム `E` が横の土管のルーチンを書く）、定理 `Run.roomEnter`、歩き `SideEntryEnd.write_right_of_left` と `SideEntryRest`（`RestOK`、`live_stepP`、`okS`、`HypW`、`clean_E`、`start_E`、`restCheck`）、`RoomMap`（`map_of_rows`、`map_run`、`start_of_rows`、`start_of_rowsF`、`clean_of_rows`、`head_of_rows`、`bump_of_rows`）。
* パート b: 部屋の最初の操作での最初の切り替えの段（`ChangesK.run₁`、`inRowsT`）と `ctl₁`、`ctlFirst₁`。
* 循環はありません。`Run.roomEnter` は `b₁ < a₂` を `ChangesK.b₁_lt_a₂` から得ていました。これは `entry₂` のルーチンのバイトを読みます。今は `Run.b₁_lt_a₂` から得ます。これは `dR_pos` と部屋の最初の操作を使います。上の定理はどれも `entry₂` を使いません。

## 道筋で変わったこと

* `ChangesBase` と `ChangesK` は引数 `L : List Nat` を持ちます。既定は `RoomMusic.restIdxM`（11 バイト）です。`entry₂ : EntryAt L V (seq a₂)`。`HurryMusic` と `HurryStart` は既定の `ChangesK` をとるので変わりません。ルーチンのバイトを読まない定理（`upStay`、`ctl₁`、`roomStay`、`run₁`、`bound₁`、`roomAt`、`pauseBits₂` など）はどの `L` にも使えます。`rt₂`、`pause₂`、`entryRest₂`、`run₂`、`bound₂`、`b₁_lt_a₂` は既定のものです。
* `Run.chg : ChangesK … (restIdxR sy nmS m0)`: 10 バイト。`Run.chgK` が 11 バイトの切り替えを出します。`Run.change₂`、`Run.start`、`Run.atCtl₀` はこれを使います（この 3 つは `Run.roomEnter` の下に移しました）。
* `Run` に新しいフィールド `dR_pos : 1 ≤ base.dR` があります。
* `RoomChecks` に 5 つの新しいフィールドがあります: `map`、`mapStart`、`mapStartF`、`sideEnd`、`sideRest`。`RoomChecks` は道筋の非公開のファイル（5 回）と急ぎの音楽の非公開のファイル（1 回）で作ります。

仮定から外したもの: `entry₂` のルーチンのバイト。加えたもの: `dR_pos`。

## 高さと画面のバッファが残る理由（測ったもの）

回 15: どちらも入るフレームで証明しました。それぞれフレームの始まりの条件のもとです（小さいプレイヤー、画面のバッファの制御が 0）。[横の土管の入口の高さ](d-2-5-4-EntryHeight-ja.md) と [横の土管の入口の画面のバッファ](d-2-5-5-EntryBuffer-ja.md) を見てください。以下は回 13 の測定です。

プログラムで、定理ではありません: `entry-y-check FM2 400`（約 1 分）。動画で部屋まで進め、部屋の中の動画のフレームから乱数の入力で 400 回走らせ、動画の入るフレームの始まりから高さ、状態、縦の速さを書きかえて 1 フレーム進めます。

| もの | 結果 |
|---|---|
| 動画 | 最初の操作は動画のフレーム 653 のあと。`t0 = C + 99`、`E = C + 111`。`t0` から `E` までの 12 フレームはすべて空中（状態 1）。入るフレームで着地する: 高さ `AD → B0` |
| 乱数で入った回数 | 157。入るフレームの終わりの高さはすべて `B0`。始まりは `AD`、`AE`、`AF`、`B0` |
| `t0` から `E` までのフレーム | 12 から 244（122 回）。そのあいだの空中のフレームは 43,492 |
| 書きかえた始まり | 960 フレーム（高さ `90` から `CF`、縦の状態 5 つ、入力 3 つ）: 55 回入り、すべて終わりの高さは `B0` |
| 入口での画面のバッファ | 位置 `00` か `07`（2 つの基準）。入るフレームの始まりのバッファの制御はどの入口でも `00` |
| コイン | 1,348 回とった。とるフレームの位置の最大は 44,528、口の左端は 49,920（21 px 先）。最後のコインから入口まで少なくとも 16 フレーム |

**高さ.** パート c は縦の状態を機械から `t0` までしか読みません（`read_vs : n ≤ t0`、`vair_of : n < t0`）。`t0` から `E` まででは、かたまりから跳ぶことはモデルの数（`Off`）にあり、機械にはありません。動画ではこの 12 フレームはすべて空中で、入るフレームが着地です。入るフレームの歩き（`SideFrame`、`SideEntryEnd`、`SideEntryRest`）は高さを追いません。部屋の歩きはブロックの地図で 0 のビットしか知らず、床の 1 のビットを知りません。だから入るフレームがどの段に着地するかを知る歩きはありません。本物のフレームでは、書きかえた始まりから入るのは終わりが `B0` のものだけです。これを出すもの: `t0` から入口までの機械の縦のバイト（パート c）、または高さを分けて床のタイルを知る入るフレームの歩き。

**画面のバッファ.** 入るフレームで最初のバッファに書くのは色の回転だけです。タイマーのコードが来るときプレイヤーのルーチンはもう動いていないので、ゲームタイマーは進みません。しかし前のフレームでコインをとると、バッファの制御が変わり、次の画面の更新は最初のバッファでなく 2 つ目を空にします。するとコインの記録が入口で最初のバッファに残ります。これを除くには入口の前の 2 フレームの位置が要ります。パート c は機械の位置を `t0` までとフレーム `E` の終わりで持ち、そのあいだのフレームでは持ちません。測ったもの: 入口の 16 フレーム以内にコインはありません。

## 仮定（Lean で証明していないもの）

* `chg.entry₂`: 入口の 10 バイトが基準の値: プレイヤーの高さ、画面のバッファ（5 バイト）、エリア音楽のバッファ、イベント音楽の待ち、足す音の長さ、レベルの番号（1-1-d-2-5）。14 回目から 9 バイト: レベルの番号は縦の土管の入口から出ます（[1-1-d-2-5-3](d-2-5-3-AreaKeep-ja.md)）。 回 15 から、高さと画面のバッファの 5 バイトは入るフレームから出ます。入るフレームが小さいプレイヤーで、画面のバッファの制御が 0 で始まるときです（[1-1-d-2-5-4](d-2-5-4-EntryHeight-ja.md)、[1-1-d-2-5-5](d-2-5-5-EntryBuffer-ja.md)）。`chg.entry₂` は 3 バイトを求め、ほかの走りのために `Run` に 2 つのフィールド `height₂`、`buffer₂` があります。
* `dR_pos`: 入口の探索は部屋の最初の操作から少なくとも 1 フレーム先まで見る。

**ファイル.** `Theorems/EntryRoutine.lean`、`Theorems/Route.lean`。`Main.lean` では生成する道筋と急ぎの音楽の証明の `RoomChecks` と、プログラム `entry-y-check`。

**再現.**
```
.lake/build/bin/smbrta entry-y-check FM2 400     # 上の表、約 1 分
```
