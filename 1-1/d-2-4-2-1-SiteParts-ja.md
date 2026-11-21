[← Back](README-ja.md) | [English](d-2-4-2-1-SiteParts.md) | [Japanese](d-2-4-2-1-SiteParts-ja.md)

# `SiteOK` の部分: 部屋でのバッファのオフセットとポインタ越しの読み

**主張.** ルートが部屋のすべてのフレームのすべての命令で求めていた条件 `SiteOK`（`chg.roomSites`）を、6 つの部分に分けました。そのうち 2 つは、ほとんどの命令で証明になりました。

* `Off`（コードが添字に使うところで、最初の画面のバッファのオフセットが 64 より小さい）は、画面のバッファの制御 0 で始まるすべてのフレームで。
* `Reads`（`LDA (zp),Y` が RAM か ROM を読む）は、ポインタが画面の更新のバッファへのポインタでない、すべての読みで。

証明しました。ROM の確認は 1 つです（部屋のフレームの歩き 2 つ。ネイティブで約 65 秒）。ルートは今、`Off` を制御 6 で始まるフレームでだけ、`Reads` をその 1 つのポインタ越しでだけ求めます。ほかの 4 つの部分は前と同じに、それぞれのフィールドとして求めます。

`tr_n(j)` はフレーム `n` の `j` 命令あとの機械です。`c(m)` は画面のバッファの制御、`off(m)` は最初のバッファのオフセットです。`L` は部屋の最後のドット（`late`）です。`InCls(T, m)` は、`m` の音楽のバイトが [部屋のフレームを通した音楽のバイト](d-2-5-1-RoomMusic-ja.md) の表 `T` のどれかの状態にあることです。

## 主張の式

```
Late(m)       :=  pc(m) ≠ idle  →  dot(m) ≤ L
Reads(m)      :=  pc(m) ≥ 0x8000  ∧  op(m) = LDA (zp),Y  →  addr(m) < 0x2000  ∨  addr(m) ≥ 0x8000
ReadsAt(Z, m) :=  同じもの。ただし命令のゼロページのオペランドが Z にあるときだけ
Read(m)       :=  pc(m) = read  →  val(m) ∈ T_tiles  ∧  (save(m) ∈ heads → val(m) ∈ T_head)
Erase(m)      :=  pc(m) = erase  →  アドレスはブロックのバッファの中
Off(m)        :=  pc(m) ∈ offAt  →  off(m) < 64
Xbit(m)       :=  pc(m) = xAt  →  x(m) & 15 ≠ 0

SiteOK(m)  ⟺  Late(m) ∧ Reads(m) ∧ Read(m) ∧ Erase(m) ∧ Off(m) ∧ Xbit(m)                  (siteOK_of)
Rest(Z, m) :=  Late(m) ∧ ReadsAt(Z, m) ∧ Read(m) ∧ Erase(m) ∧ Xbit(m)
Z₁         :=  ptrS = { 画面の更新の最初の読みのポインタ }

music_frame0  :  musicCheck(T),   RoomCond(r, K_M, m),   InCls(T, m),   c(m) = 0,   ∀ j, Rest(Z₁, tr(j))                →   ∀ j, SiteOK(tr(j))
music_frame6  :  musicCheck(T),   RoomCond(r, K_M, m),   InCls(T, m),   c(m) = 6,   ∀ j, Rest(Z₁, tr(j)) ∧ Off(tr(j))     →   ∀ j, SiteOK(tr(j))
music_sites_of_rows :
      [b, a) で RoomMap.map_of_rows の条件,   keepCheck,   startCheckC,   RoomMusic.Facts(T),   musicCheck(T),   Room(seq b),
      ∀ n ∈ [b, a), ∀ j, Rest(Z₁, tr_n(j)),     ∀ n ∈ [b, a),  c(seq n) = 6  →  ∀ j, Off(tr_n(j))
      →   ∀ n ∈ [b, a), ∀ j, SiteOK(tr_n(j))

Run.roomSites :  ∀ n ∈ [b₁, a₂),  ∀ j,  SiteOK(tr_n(j))                       （定理。前はフィールド chg.roomSites）
```

`K_M` は `RoomMusic` の部屋の条件（`knownM`）です。`chg` の新しいフィールド（どれも、すべての `n ∈ [b₁, a₂)` とすべての `j` について）:

```
roomLate  : Late(tr_n(j))          roomReads : ReadsAt(Z₁, tr_n(j))          roomRead : Read(tr_n(j))
roomErase : Erase(tr_n(j))         roomXbit  : Xbit(tr_n(j))                 roomOff₆ : c(seq n) = 6  →  Off(tr_n(j))
```

Lean: `Theorems/SiteParts.lean`:

* 部分、`Rest`、`ReadsAt`、`ptrS`。
* 状態での確認: `offOK`、`off_of_ok`、`hiOK`、`readsOK`、`reads_of_ok`。
* すべての状態で確認をする `RoomMusic` の歩き: `walkPC`、`frame_of_walkPC`、`cfgPC`、`walkCheckPC`、`music_frame`。
* ROM で: `musicCheck`、`music_frame0`、`music_frame6`、`cond_at`、`music_sites_of_rows`。
* `BufferControl` の歩きでの最初の版（`walkC`、`frame_of_walkC`、`siteCheck`、`sites_of_rows`）: 音楽のポインタ越しの読みを除いて同じことを証明します。ルートはこれを使いません。

`Theorems/Route.lean`: 6 つのフィールド、`ChangesBase.roomRest`、`ChangesK.roomSites`、`Run.roomSites`、`lateL_of`。`Theorems/BufferEnd.lean`: `FactsE.music`。非公開の確認は `Proof/SiteMusic.lean` の `buffer_music_check` です。公開のファイルにゲームのデータはありません。ポインタは 1 つの記号の位置で ROM から読みます。

## しくみ

**すべての状態で条件を確かめる歩き.** 歩きは [部屋のフレームを通した音楽のバイト](d-2-5-1-RoomMusic-ja.md) のもの（`RoomPause.pstep`）です。部屋のフレームを抽象機械でたどり、音の処理を呼ぶところで状態を音楽の表の状態ごとに分けます。だから音の処理は音楽のバイトが分かった状態で進みます。ここでは、その条件が画面のバッファの制御（0 か 6）も知り、探索は最初のバッファのオフセットが違う状態を分けておきます。`walkPC` はこの歩きに、たどり着くすべての状態とフレームの終わりで、もう 1 つの確認 `chk` を加えたものです。状態 `A` が機械 `m` を覆い、`chk(A)` が成り立ち、`m` が残りを満たせば、`m` は `SiteOK` を満たします。フレームの定理（`frame_of_walkPC`）は命令を 1 つずつ進みます。命令 `j` での状態は、`j` より前の命令での `SiteOK` だけから出ます。その状態での確認が、`j` での足りない部分を与えます。だからフレームは各命令で残りだけを求め、6 つ全部を与えます。歩きはフレームの終わりでそれ以上を求めません（`cfgPC`）。フレームの定理が与えるのは `SiteOK` だけで、次のフレームの始めの条件は、ルートがすでに持つ歩きから出ます。

**オフセット.** 制御 0 で始まるフレームでは、始めの画面の更新が最初のバッファのオフセットに 0 を書きます。そのあとフレームのコード（プレイヤーの色、色の回転、スコア、コイン、タイマーの数字）は、分かっている長さを足します。制御 0 からの歩きは、コードがオフセットを添字に使うすべての状態で、オフセットが 64 より小さいと知っています（`offOK`: 分かっているビットでの最大の値が 64 より小さい）。

**読み.** 各 `LDA (zp),Y` で、確認は、ポインタの上のバイトが `0x1E` 以下か `0x80` 以上だと状態が知っていることを求めます（`SideChangeEnd.ptrHiOK`）。そうなら、どのアドレス `ポインタ + Y` も RAM か ROM にあります（`SideChangeEnd.wide_ok`、`RoomBlocks.readAddr_eq`）。音楽のポインタは音楽のバイトの 1 つなので、歩きはそれを通るどの読みでも知っています。画面の更新のポインタは、7 の状態（制御 0 から）と 11 の状態（6 から）で知りません。記録の長さだけバッファの中を進み、歩きはその長さを知らないからです。だから確認はこのポインタ越しの読みを求めず（`readsOK`）、ルートがそこで `Reads` を求めます（`ReadsAt(Z₁, ·)`）。

**フレームを順に.** `music_sites_of_rows` は部屋のフレームを 1 つずつ進みます。フレーム `n` での次のものは、`n` より前のフレームの `SiteOK` だけを使います。地図のビットを持つ部屋の条件（フレーム `n − 1` までの `RoomMap.cond_of_rows` と、`RoomMap.room_stepT` の 1 歩）、制御が 0 か 6 であること（`BufferControl.ctl_of_rows`）、音楽のバイトが表のどれかの状態にある `RoomMusic` の条件（`RoomPause.pause_step` でフレームからフレームへ運ぶ。部屋の最初の操作では 1 つ目の切り替えの段から、`RoomMusic.start_of_invL`）。制御 0 で始まるフレームは `music_frame0` から 6 つ全部を、6 で始まるフレームは `music_frame6` とフィールド `roomOff₆` から得ます。

**大きさ.** 制御 0 からの歩き: 表は 78,693 状態。6 から: 216,532 状態。2 つの歩きの確認: ネイティブで約 65 秒で、数秒より長くかかります。非公開の `Proof.SiteMusic`: ほかの仕事と同時の `prove.py` 全体の中で 67 秒。

**最初の版.** [BufferControl](d-2-5-5-1-BufferControl-ja.md) の歩き（制御を知る部屋の歩き。音楽のバイトは知らない）でも同じ確認が通ります（`siteCheck`、ネイティブで 9.6 秒）。ただし音楽のポインタ越しの読みは除きます。その歩きは 187 の状態（0 から）と 197 の状態（6 から）でポインタの上のバイトを知りません。場所は画面の更新の 4 か所と音楽の処理の 5 か所です。

## 制御 6 で始まるフレームで `Off` が残るわけ

コインを消すフレームは制御を 6 にします。次のフレームの画面の更新は 2 つ目のバッファを描き、最初のバッファのオフセットを 0 に戻しません。だからそのフレームの始めのオフセットは、コインのフレームが残したものです。コインのフレームは最初のバッファに 14 バイトを足します（コインの 2 桁とスコアの 6 桁。それぞれに 3 バイトの頭）。タイマーの数字や色がさらに足します。コインのフレームは続くことがあります（1 フレームで消すコインは 1 つで、プレイヤーは一度にいくつものコインに触れられます）。だから上限には続けて取るコインの数が要りますが、この歩きはそれを知りません。測ったもの: 制御 6 から、始めのオフセットを知らないとき、歩きは 92 の状態でオフセットが 64 より小さいと知りません。

## 測ったもの（定理ではない）

`buffer-ctl-check FM2 100 sites`（exit 0）: ムービーの部屋のフレームから始めた自分の走り。小さいプレイヤーと大きいプレイヤーで 100 回ずつ。

| プレイヤー | 走り | フレーム | 制御 6 で始まるフレーム | その始めの最初のバッファのオフセット（最大） | そのフレームでの使うところでのオフセット（最大） | 画面の更新か音楽のポインタ越しの読み | `SiteOK` のどれかの部分を満たさない命令 |
|---|---|---|---|---|---|---|---|
| 小さい | 100 | 42,438 | 316 | 42 | 41 | 105,632 | 0 |
| 大きい | 100 | 42,452 | 403 | 55 | 46 | 107,760 | 0 |

この 2 つのポインタ越しの読みは、どれも RAM（画面のバッファ）か ROM（音楽のデータ）を読みます。これらの走りでは、制御 6 で始まるフレームの始めのオフセットは 55 になります。そのフレームでコインを取ると 14 バイト足されて 64 を超えます。だから、そのフレームの始めのオフセットの上限があっても、この歩きでは `Off` は出ません。そのフレームでコインを取らないこと、つまり位置も知る必要があります。

## ほかのパートから使うもの

* パート c: `RoomMap.cond_of_rows`、`RoomMap.start_of_rows`、`RoomMap.room_stepT`、`MapFacts`、`startCheckT`。`RoomBlocks.readAddr_eq`、`ptrZ`、`operand`。`ChangesBase.roomStay`、`ChangesK.roomAt`。
* パート b: `ChangesK.run₁`、`PipeRunK.inRowsT`、`ChangesBase.ctlFirst₁`、`ChangesBase.ctl₁`。`SideChangeEnd.ptrHiOK`、`ptrWide`、`wide_ok`。
* パート a: `Run.entry₁`。
* パート d: `BufferControl`（`keepCheck`、`startCheckC`、`ctl_of_rows`、`cond0`、`cond6`、`ref6`）、`RoomMusic`（`Facts`、`regM`、`knownM`、`start_of_invL`、`roomCond_append`）、`RoomPause`（`pstep`、`s_pstep`、`pause_step`、`cfgOfP`、`InCls`、`Ph`）、`StepWrites`（`tabOK`、`le_pc_spent`）、`EntryBuffer`、`EntryHeight`（最初の版）。
* 循環はありません。どれも `roomSites` も `Run.roomSites` も使いません。`ChangesK.roomSites` が使うのはフィールド `roomLate`、`roomReads`、`roomRead`、`roomErase`、`roomXbit`、`roomOff₆`、`ctl₁`、`ctlFirst₁`、1 つ目の切り替えの段と確認だけです。

## ルートで変わったこと

* なくしたフィールド: `chg.roomSites`（`∀ n ∈ [b₁, a₂), ∀ j, SiteOK(tr_n(j))`）。
* 加えたフィールド: `roomLate`、`roomReads`（画面の更新のポインタ越しだけ）、`roomRead`、`roomErase`、`roomXbit`、`roomOff₆`（制御 6 で始まるフレームだけ）。
* `Run.roomSites hR hB hK R` が前のフィールドの主張を与えます。`chg.roomSites` を使っていた部屋の定理は、今は部屋の確認 `hR` もとります（`Run.roomBump`、`roomArrive`、`roomBefore`、`roomStR`、`roomReach`、`roomCut`、`roomVert`、`roomAir`、`roomHigh`、`roomLand`、`roomWall`、`roomHighJ`、`roomHighA`、`roomCorner`、`roomStand`、`roomFloor`、`roomJump`、`roomBlocks`、`roomPair`、`roomV0`、`roomKeepA`、`roomKeep`、`roomBlocksTrace`、`roomCollisionMap`、`roomFootMap`）。`Run.roomTime` は `roomLate` を使います。
* `RoomChecks.buffer`（`BufferEnd.FactsE`）に新しいフィールド `music` があります。表を持つ `RoomMusic` の事実と、同じ表での `musicCheck` です。

## 仮定（Lean で証明していないもの）

* 部屋のフレームの各命令での `Late`、`Read`、`Erase`、`Xbit`。前と同じです（項目 1-1-d-2-4-2）。歩きがこれらの何を知っているかはラウンド 26 で測りました（[部屋の画面のページ](d-2-4-ScreenPage-ja.md)）。各道筋でのドットの上限と、いくつものフレームにわたる位置と高さが要ります。
* 画面の更新のバッファへのポインタ越しの `Reads`。
* 制御 6 で始まるフレームでの `Off`。
