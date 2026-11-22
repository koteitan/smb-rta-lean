[← Back](README-ja.md) | [English](d-2-4-2-2-BufferRecords.md) | [Japanese](d-2-4-2-2-BufferRecords-ja.md)

# 画面のバッファのレコード: 部屋での画面の更新の読みとバッファのオフセット

**主張.** 部屋のフレームでは、画面の更新は前のフレームが書いた画面のバッファを読む。前のフレームが画面のバッファの制御 0 で始まったなら、そのフレームの歩きは、書いたレコードと残した 1 つ目のバッファのオフセットを知っている。だから次のフレームでは:

* 画面の更新がバッファへのポインタ越しに読む読みは、どれも RAM を読む。
* 次のフレームが制御 6 で始まるなら、1 つ目のバッファのオフセットは、コードが使うところでいつも 64 未満。

これは証明した。ROM の上の検査は 1 つ（部屋のフレームの 4 つの歩き）。ラウンド 27 までルートは、画面の更新のポインタ越しの `Reads` を部屋のすべてのフレームで、`Off` を制御 6 で始まるすべてのフレームで求めていた。いまは:

* 画面の更新のポインタ越しの `Reads` は、部屋の最初のフレームと、制御 6 で始まるフレームの次のフレームでだけ求める。
* `Off` は、制御 6 で始まるフレームの次の、制御 6 で始まるフレームでだけ求める。

ラウンド 29: ルートは `RoomLate.recCheckT` を使う。この検査で、歩き (ii) と (iii) がすべての状態で時間も確かめる（[部屋のフレームの時間](d-2-4-2-3-RoomLate-ja.md)）。

`tr_n(j)` はフレーム `n` の `j` 命令あとの機械。`c(m)` は画面のバッファの制御。`Z₁` は画面の更新のポインタ（`SiteParts.ptrS`）。`Rest(Z, m)` は `m` での `Late ∧ ReadsAt(Z) ∧ Read ∧ Erase ∧ Xbit`（[`SiteOK` の部分](d-2-4-2-1-SiteParts-ja.md)）。`Rest(∅, m)` は読みを何も求めない。

## 主張の式

```
Pat(s, m)        :=  ∀ (i, v) ∈ s,  m.ram[i] = v                      （パターン: いくつかのバイトが決まった値）
InPat(v, L, m)   :=  c(m) = v  ∧  ∃ s ∈ L,  Pat(s, m)
U(n)             :=  n = b  ∨  (b < n  ∧  c(seq(n − 1)) = 6)          （部屋の最初のフレーム、または制御 6 で始まるフレームの次）

rec_frame1 :  recCheck(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  c(m) = 0,  ∀ j, Rest(Z₁, tr(j))
              →  (∀ j, SiteOK(tr(j)))  ∧  (InPat(0, L, frame(m, i)) ∨ InPat(6, L₆, frame(m, i)))
rec_frame2 :  同じ。ただし c(m) = 0 のかわりに InPat(0, L, m)、Rest(Z₁, tr(j)) のかわりに Rest(∅, tr(j))
rec_frame3 :  recCheck(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  InPat(6, L₆, m),  ∀ j, Rest(∅, tr(j))                →   ∀ j, SiteOK(tr(j))
rec_frame4 :  recCheck(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  c(m) = 6,  ∀ j, Rest(Z₁, tr(j)) ∧ Off(tr(j))      →   ∀ j, SiteOK(tr(j))

records_sites_of_rows :
      [b, a) での RoomMap.map_of_rows の条件、 keepCheck、 startCheckC、 RoomMusic.Facts(T)、 recCheck(T, L, L₆)、 Room(seq b)、
      ∀ n ∈ [b, a), ∀ j, Rest(∅, tr_n(j))、
      ∀ n ∈ [b, a),  U(n)  →  ∀ j, ReadsAt(Z₁, tr_n(j))、
      ∀ n ∈ (b, a),  c(seq n) = 6  ∧  c(seq(n − 1)) = 6  →  ∀ j, Off(tr_n(j))
      →   ∀ n ∈ [b, a), ∀ j, SiteOK(tr_n(j))
```

`chg` の変わった 2 つのフィールド（すべての `j` について）:

```
roomReads :  b₁ ≤ n < a₂  ∧  (n = b₁  ∨  (b₁ < n  ∧  c(seq(n − 1)) = 6))   →  ReadsAt(Z₁, tr_n(j))
roomOff₆  :  b₁ < n < a₂  ∧  c(seq n) = 6  ∧  c(seq(n − 1)) = 6           →  Off(tr_n(j))

ラウンド 27 まで:   roomReads :  b₁ ≤ n < a₂  →  ReadsAt(Z₁, tr_n(j))        roomOff₆ :  b₁ ≤ n < a₂  ∧  c(seq n) = 6  →  Off(tr_n(j))
```

`L` と `L₆` はパターンのリスト、`T` は音楽の表。プログラムが見つける。検査は見つけ方によらない。

* `L` は 1 つ目のバッファの 6 つのパターン: レコードなし、色のレコード、ほかの色の色のレコード、タイマーのレコード、両方の 2 つ。
* `L₆` は 6 つのパターン: コインをとったフレームのあとの 1 つ目のバッファのオフセットとレコード（コインとスコアのレコード、それに色かタイマーのレコードか、どちらもなし）と、コインを消すときに書く空のブロックの、2 つ目のバッファの 2 つのレコード。

このページにはバイトの値を書かない。非公開の証明がリストを持つ。

Lean: `Theorems/BufferRecords.lean`:

* パターン: `Pat`、`knowsPat`、`refPat`、`knownPat`、`patOK`、`cond_pat`、`pat_of_knows`
* フレームの終わりのクラス: `ctlIs`、`anyPat`、`fin0`、`InPat`、`end0`
* 終わりつきの 1 フレーム: `frame_of_walkPCE`
* 歩き: `preWalk`、`searchB`、`cfgB`（証明の一部ではない）、`walkCheckB`、`BOK`、`bok_of_check`、`frameB`
* ROM の上: `fpcOf`、`ptrBytes`、`noRegs`、`zO`、`zOC`、`walk1` から `walk4`、`recCheck`、`rec_frame1` から `rec_frame4`
* 部屋のフレーム: `U`、`records_sites_of_rows`

`Theorems/Route.lean`: フィールド `roomReads`、`roomOff₆`、`ChangesBase.roomRest`（いまは `Rest(∅)`）、`ChangesK.roomSites`。`Theorems/BufferEnd.lean`: `FactsE.music`（いまは `recCheck` と 2 つのリスト）。非公開の検査は `Proof/SiteMusic.lean` の `buffer_records_check`。リスト `recL0`、`recL6` は `Proof/RoomPause.lean` にある。

## しくみ

**フレームの始まりのクラス.** 制御 0 で始まるフレームは、画面の更新で始まる。画面の更新は 1 つ目のバッファを描き、1 つ目のバッファのオフセットを 0 にし、その始めに終わりの印を置く。それからフレームのコードが 1 つ目のバッファにレコードを書く。レコードは 3 バイトの見出し（画面の場所と長さ）とデータ。見出しは ROM から来る。制御 0 からの `RoomMusic` の歩きは、オフセットのちがう状態を分けておく。だから歩きはフレームの終わりで、すべての見出し、終わりの印、オフセットを知る。フレームがコインを消すなら、2 つ目のバッファの決まった場所に空のブロックの 2 つのレコードを書き、制御を 6 にする。だから制御 0 からのフレームはどれも、2 つのクラスのどちらかで終わる（`fin0`）:

* `InPat(0, L, ·)`: 制御 0、1 つ目のバッファの見出しと終わりの印が `L` のパターン
* `InPat(6, L₆, ·)`: 制御 6、1 つ目のバッファのオフセット、見出しと終わりの印、2 つ目のバッファの見出しと終わりの印が `L₆` のパターン

**パターンからの画面の更新.** 次のフレームの画面の更新は、そのクラスのバッファを読む（0 なら 1 つ目、6 なら 2 つ目）。パターンを知っていれば、歩きは各レコードの長さを知る。だから各レコードのあとのポインタを知り、ポインタ越しの読みはどれも RAM の読みになる（読みの検査 `SiteParts.readsOK` で、外すポインタなし）。制御 6 からのフレームは 1 つ目のバッファのオフセットを 0 にしない。`L₆` のパターンからなら歩きはそのオフセットを知り、オフセットを分けておくので、コードが使うところでいつも 64 未満と知る（`SiteParts.offOK`）。

**4 つの歩き**（`recCheck`）。どれも、すべての状態で検査をする `RoomMusic` の歩き（`SiteParts.walkPC`）:

| 歩き | 始まり | 各状態での検査 | フレームの終わりで | 表 | ネイティブ |
|---|---|---|---|---|---|
| (i) `walk1` | 制御 0、バッファは知らない | オフセットが 64 未満。読み、ただし `Z₁` 越しを除く | `fin0` | 78,693 状態 | 18 秒 |
| (ii) `walk2` | `L` の 6 つのパターン、制御 0 | オフセットが 64 未満。すべての読み | `fin0` | 32,154 状態 | 8 秒 |
| (iii) `walk3` | `L₆` の 6 つのパターン、制御 6 | オフセットが 64 未満。すべての読み | なし | 182,438 状態 | 44 秒 |
| (iv) `walk4` | 制御 6、バッファは知らない | 読み、ただし `Z₁` 越しを除く | なし | 216,532 状態 | 38 秒 |

歩き (i) と (iv) はラウンド 27 のもの（`SiteParts.musicCheck`）。歩き (i) はいまフレームの終わりで `fin0` も確かめる。歩き (i)、(ii)、(iii) の探索は 1 つ目のバッファのオフセットを分けておく。(iii) の探索は制御も分けておく。

**パターンからの歩きの 2 つの細かいこと.** 歩き (ii) と (iii) の探索は、画面の更新のループの状態をループの頭で合わせて、ポインタを失う。そこで、それぞれの始まりを、まず 1 つずつ画面の更新の中を歩く（`preWalk`）。探索はそのあと、画面の更新の呼び出しのあとの場所（`fpcOf`）から始める。そこで歩きはポインタの 2 バイト（`ptrBytes`）を忘れるので、状態はまた合わさる。探索の助け（aids）には、画面の更新の中でレジスタを忘れる場所が 3 つある。パターンからの歩きはその場所を使わない（`noRegs`）。そこで歩きはレコードの長さをレジスタに持っている。探索は画面の更新のあとから始まるので、ほかは変わらない。

**フレームを順に.** `records_sites_of_rows` は、`SiteParts.music_sites_of_rows` と同じに部屋のフレームを 1 つずつとる。もう 1 つ、フレームの始まりのクラスを運ぶ。部屋の最初のフレームは `U`。制御 0 からのフレームは、次のフレームに `InPat(0, L, ·)` か `InPat(6, L₆, ·)` を与える（歩き (i)、(ii)）。制御 6 からのフレームは何も与えない（歩き (iii)、(iv)）。次のフレームは `U` になる。だからどのフレームも 3 つのどれかにある:

* `InPat(0, L, ·)`: 歩き (ii)。`Rest(∅)` だけから
* `InPat(6, L₆, ·)`: 歩き (iii)。`Rest(∅)` だけから
* `U` で制御 0: 歩き (i)。`Rest(Z₁)` から、つまりフィールド `roomReads` を使う
* `U` で制御 6: 歩き (iv)。`Rest(Z₁)` と `Off` から。このとき前のフレームは制御 6 で始まった（部屋の最初のフレームは 0 で始まる）ので、フィールド `roomOff₆` が使える

**大きさ.** 検査はネイティブでおよそ 111 秒。ラウンド 27 の `musicCheck`（歩き (i) と (iv) だけ）はおよそ 65 秒だった。非公開の証明 `Proof.SiteMusic` がこの検査をする。数秒より長い。

## 制御 6 で始まるフレームの次のフレームが残る理由

制御 6 で始まるフレームは 2 つ目のバッファを描き、1 つ目のバッファのオフセットを 0 にしない。そのレコードは、コインのフレームが残したレコードのあとに続く。歩き (iii) はそれを知っているが、フレームの終わり方は多く、次のフレームはそのすべてを読む。歩き (iii) の終わりのパターンを `L` に足すと（29 増えて 35）、歩き (ii) は 20 分たっても終わらなかった。だから歩き (iii) はフレームの終わりで何も求めない。歩き (iv) はバッファについて何も知らずに始まる。1 つ目のバッファのオフセットを知らず、歩きの中ではフレームのレコードが 1 つ目のバッファを越えて 2 つ目に入りうる。測ったこと: オフセットを分けない `BufferControl` の歩きでは、制御 6 で終わるフレームのどれも、2 つ目のバッファのバイトを 1 つも知らない。だからこれらのフレームの証明には、いくつものフレームにわたるオフセットの上限がいる。続けてとるコインの数で、位置から来る。

## 測ったこと（定理ではない）

`buffer-ctl-check FM2 100 recreal`（exit 0）: 部屋の本物のフレームで、各フレームの始まりのクラス。動画のフレームと、そこからの自分の走り（小さいのと大きいの、それぞれ 100、`sites` と同じ）。制御 0 からのフレームの次のフレームは、パターンで始まるはず。定理はそう言い、走りも合う。

| フレーム | `L` のパターン | `L₆` のパターン | 部屋の最初 | 制御 6 からのフレームの次（`roomReads` を求める） | そのうち 6 で始まる（`roomOff₆` を求める） | 制御 0 からの次なのにパターンなし |
|---|---|---|---|---|---|---|
| 動画: 入るフレームの前の部屋の 111 フレーム | 87 | 10 | 1 | 13 | 3 | 0 |
| 自分の走り、小さい: 100 走り、51,791 フレーム | 50,868 | 422 | – | 501 | 69 | 0 |
| 自分の走り、大きい: 100 走り、55,755 フレーム | 54,798 | 428 | – | 529 | 92 | 0 |

だから動画では、ルートは画面の更新のポインタ越しの `Reads` を 111 フレームのうち 14 で求める（ラウンド 27 まで: 111 すべて）。`Off` は 3 で求める（ラウンド 27 まで: 13）。自分の走りは部屋の中の動画のフレームから始まるので、どれも部屋の最初のフレームではない。

## ほかの部分から使うもの

* 部分 c: `RoomMap.cond_of_rows`、`RoomMap.room_stepT`、`MapFacts`、`startCheckT`（`SiteParts.cond_at` を通して）。`ChangesBase.roomStay`、`ChangesK.roomAt`
* 部分 b: `ChangesK.run₁`、`PipeRunK.inRowsT`、`ChangesBase.ctlFirst₁`、`ChangesBase.ctl₁`。`SideChangeEnd.ptrHiOK`、`wide_ok`（`SiteParts.reads_of_ok` を通して）
* 部分 d: `SiteParts`（`walkPC`、`live_stepPC`、`chkP_of_walk`、`chk0`、`readsOK`、`reads_of_ok`、`off_of_ok`、`siteOK_of_rest`、`knownMC`、`keepOff`、`ptrS`）。`BufferControl`（`keepCheck`、`startCheckC`、`ctl_of_rows`、`start_ctl`、`cond0`、`cond6`、`ref6`）。`RoomMusic`（`Facts`、`regM`、`knownM`、`start_of_invL`、`roomCond_append`）。`RoomPause`（`pstep`、`searchP`、`routeP`、`aidsP`、`keyP`、`pause_step`、`InCls`、`Ph`）。`StepWrites.tabOK`
* 循環はない: これらはどれも `roomSites` も `Run.roomSites` も使わない。`ChangesK.roomSites` が使うのは、フィールド `roomLate`、`roomReads`、`roomRead`、`roomErase`、`roomXbit`、`roomOff₆`、`ctl₁`、`ctlFirst₁`、1 つ目の切り替えの段と検査だけ

## ルートで変わったこと

* 狭めたフィールド: `roomReads`（部屋の最初のフレームと、制御 6 からのフレームの次のフレームだけ）と `roomOff₆`（制御 6 からのフレームの次の、制御 6 からのフレームだけ）。
* `RoomChecks.buffer`（`BufferEnd.FactsE.music`）: `∃ T, RoomMusic.Facts(T) ∧ musicCheck(T)` のかわりに `∃ T L₀ L₆, RoomMusic.Facts(T) ∧ recCheck(T, L₀, L₆)`。
* 1 つの定理の結論が変わった: `ChangesBase.roomRest` はいま `SiteParts.Rest []` を与える（前は `Rest ptrS`）。使うのは `ChangesK.roomSites` だけ。`route_1_1` はいまも `1748 + j ≤ L` を結論する。

## 仮定（Lean では証明していない）

* 部屋の最初のフレームと、制御 6 で始まるフレームの次のフレームでの、画面の更新のポインタ越しの `Reads`。
* 制御 6 で始まるフレームの次の、制御 6 で始まるフレームでの `Off`。
* 部屋のフレームの各命令での `Late`、`Read`、`Erase`、`Xbit`（前と同じ）。
