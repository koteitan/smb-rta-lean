[← Back](README-ja.md) | [English](d-2-4-2-4-LoopTime.md) | [Japanese](d-2-4-2-4-LoopTime-ja.md)

# ループの後ろへのジャンプからの部屋のフレームの時間

**主張.** 部屋のすべてのフレームで、アイドルループ以外の命令はすべてフレームの終わりの 6000 ドット以上前に走る。ただし、歩きが回数を知らないループの後ろへのジャンプがドット 9,000 までに走るとする。部屋の最初のフレームと、画面のバッファの制御 6 で始まるフレームの次のフレーム（フレーム `U`）では、画面の更新のバッファのレコードのループと音のルーチンのもの。ほかのフレームでは音のルーチンのもの。

これは証明した。ROM の上の検査は 1 つ。ラウンド 29 まで、ルートはフレーム `U` のすべての命令で `Late`（アイドルループ以外でドットが `L` = 83,342 以下）を求め（フィールド `roomLate`）、ほかのフレームでは音のルーチンのコードの命令がすべてドット 9,000 までに走ることを求めていた（`roomLateS`）。今は次のとおり。

* `roomLate` はなくなった。代わりに `roomLateU` が、フレーム `U` で、画面の更新のループの後ろへのジャンプ（2 命令）と音のルーチンのコードの後ろへのジャンプ（89 命令）だけを求める。
* `roomLateS` は、ほかのフレームで、音のルーチンのコードの後ろへのジャンプだけを求める。コードのすべての命令ではない。

その少しの命令では、上限は `L` ではなく 9,000。だから `roomLateU` はそこでは `roomLate` より多くを求める（小さいドット）。ほかの場所では何も求めない。

**コインを消すところも.** コインを消す `STA (zp),Y` では、歩きはポインタの上のバイト、つまりブロックのバッファのページを知っている。だから消す書き込みは RAM の中で、ブロックのバッファの始め以降に入る。これは証明した。フィールド `roomErase` は今は残りだけを求める: 書き込みはブロックのバッファの終わりより前（`EraseEnd`）。前は `Erase`: RAM の中、始め以降、終わりより前。

ラウンド 31: 歩きはポインタの下のバイトの足し算の前で状態を分ける。だから最初のブロックのバッファへのポインタを通る消去は、終わりより前に書くことも証明した。`roomErase` は今は、ポインタが 2 つめのブロックのバッファの始め以降の消去だけに `EraseEnd` を求める（`EraseTwo`）: [最初のブロックのバッファでのコインの消去](d-2-4-2-5-EraseSplit-ja.md)。

`tr_n(j)` はフレーム `n` の `j` 命令あとの機械。`pc`、`dot` はそのプログラムカウンタとフレームの中のドット。`idle` はアイドルループ。`snd`、`rep`、`upd` は `SoundEngine`、`RepeatByte`、`UpdateScreen` のアドレス。`rom(p)` は `p` の ROM のバイト。`A.hi` は抽象状態が許す最後のドット。`U(n)`、`InPat`、`RestS`、`timeOK` は [画面のバッファのレコード](d-2-4-2-2-BufferRecords-ja.md) と [部屋のフレームの時間](d-2-4-2-3-RoomLate-ja.md) と同じ。

## 主張の式

```
back(p)          :=  (rom(p) & 0x1F = 0x10  ∧  rom(p + 1) ≥ 0x80)            負のオフセットの相対分岐
                   ∨ (rom(p) = JMP  ∧  rom(p + 1) + 256 · rom(p + 2) ≤ p)      p 以下のアドレスへの JMP
sndQ(p)          :=  snd ≤ p  ∧  back(p)
scrQ(p)          :=  sndQ(p)  ∨  (rep ≤ p < upd + 16  ∧  back(p))
LateS(q, m)      :=  q(pc(m))  →  dot(m) ≤ 9,000
EraseEnd(m)      :=  pc(m) = erase  →  addr(m) & 0x7FF < bufLo + bufN          （addr(m): STA (zp),Y が書くアドレス）
eraseOK(A)       :=  pc(A) ≠ erase  ∨  （ポインタの上のバイト h を知る  ∧  256 h + 510 < 2048  ∧  bufLo ≤ 256 h  ∧  0x8000 ≤ pc(A) + 1）
erase_of_ok      :  Sim(A, m) ∧ eraseOK(A) ∧ EraseEnd(m)  →  Erase(m)
RestU(m)         :=  ReadsAt(Z₁, m) ∧ Read(m) ∧ EraseEnd(m) ∧ Xbit(m) ∧ LateS(scrQ, m)
RestB(m)         :=  LateS(sndQ, m) ∧ Read(m) ∧ EraseEnd(m) ∧ Xbit(m)

rec_frame1B      :  recCheckB(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  c(m) = 0,  ∀ j, RestU(tr(j))
                    →  (∀ j, SiteOK(tr(j)))  ∧  (InPat(0, L, frame(m, i)) ∨ InPat(6, L₆, frame(m, i)))
rec_frame2B      :  recCheckB(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  InPat(0, L, m),  ∀ j, RestB(tr(j))
                    →  (∀ j, SiteOK(tr(j)))  ∧  (InPat(0, L, frame(m, i)) ∨ InPat(6, L₆, frame(m, i)))
rec_frame3B      :  recCheckB(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  InPat(6, L₆, m),  ∀ j, RestB(tr(j))   →   ∀ j, SiteOK(tr(j))
rec_frame4B      :  recCheckB(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  c(m) = 6,  ∀ j, RestU(tr(j)) ∧ Off(tr(j))   →   ∀ j, SiteOK(tr(j))

loop_sites_of_rows :
      late_sites_of_rows の条件（recCheckT(T, L, L₆) の代わりに recCheckB(T, L, L₆)）、
      ∀ n ∈ [b, a), ∀ j,  Read(tr_n(j)) ∧ EraseEnd(tr_n(j)) ∧ Xbit(tr_n(j))、
      ∀ n ∈ [b, a),  U(n)  →  ∀ j, LateS(scrQ, tr_n(j))、
      ∀ n ∈ [b, a),  ¬U(n) →  ∀ j, LateS(sndQ, tr_n(j))、
      画面の更新のポインタ越しの Reads（U で）と Off（6 の次の 6 で）のラウンド 28 のフィールド
      →   ∀ n ∈ [b, a), ∀ j, SiteOK(tr_n(j))
```

`chg` の変わったフィールド（すべての `n ∈ [b₁, a₂)` とすべての `j` で）:

```
roomLate   :  U(n)  →  Late(tr_n(j))                       なくなった
roomLateU  :  U(n)  →  LateS(scrQ, tr_n(j))                新しい
roomLateS  :  ¬U(n) →  LateS(sndQ, tr_n(j))                前は: snd ≤ pc(tr_n(j)) → dot(tr_n(j)) ≤ 9,000
roomErase  :  EraseEnd(tr_n(j))                            前は: Erase(tr_n(j))
```

`recCheckB` は [画面のバッファのレコード](d-2-4-2-2-BufferRecords-ja.md) の `recCheck` の 4 つの歩きを、すべて時間つき（`RoomLate.walkST`）で歩く。バッファのパターンからの (ii) と (iii) は `sndQ` だけで最後のドットを 9,000 にクランプする。歩きが知らないバッファからの (i) と (iv) は `scrQ` だけでクランプする。どの歩きもすべての状態で `timeOK` と `eraseOK` を確かめるので、すべての命令で `Late` が成り立ち、`EraseEnd` が成り立つところでは `Erase` も成り立つ。`ChangesK.roomSites` は `loop_sites_of_rows` を使う。`BufferEnd.FactsE.music` は `recCheckB` を求める。

Lean: `Theorems/LoopTime.lean`（`backJ`、`sndQ`、`scrQ`、`EraseEnd`、`eraseOK`、`ptr_val`、`addr_page`、`and7FF_of_lt`、`erase_of_ok`、`chk1B`、`chk2B`、`chk4B`、`walk1B` から `walk4B`、`recSmall`、`recCheckB`、`recCheckB_of`、`RestU`、`RestB`、`rec_frame1B` から `rec_frame4B`、`loop_sites_of_rows`）、`Theorems/RoomLate.lean`（ラウンド 30: `LateS`、`sclamp`、`walkST`、`searchST`、`cfgBT`、`walkCheckST`、`STOK`、`frameST` は `SoundEngine` のアドレスの代わりにプログラムカウンタの上の述語を取る。`sndAll` はラウンド 29 の述語）、非公開の `Proof/SiteMusic1.lean` から `Proof/SiteMusic4.lean`（`buffer_walk1` から `buffer_walk4`、歩き 1 つずつ）と `Proof/SiteMusic.lean`（`buffer_records_small`。`buffer_records_check` は今は `recCheckB`、`recCheckB_of` から）。ROM を使わない定理は公理 `propext`、`Classical.choice`、`Quot.sound` だけを使う。

## 仕組み

**時間が増えるところ.** 歩きは命令ごとのサイクルを最後のドット `hi` に足す。たいていのループの回数は知っている: 知っている添字のループや、画面のフラグの待ち（状態を読むとフラグのドットで状態を分ける）。ラウンド 29 は、`hi` が限りなく増えるのは歩きが回数を知らないループだけだと見つけた: 音のルーチン（知らないポインタとオフセットで音楽のデータを追う）と、歩きが知らないバッファからの、画面の更新のレコードのループ。

**後ろへのジャンプでのクランプ.** ループはどれもどこかで後ろへ戻る: その命令の 1 つは、自分のアドレス以下のアドレスへ分岐するかジャンプする。だから歩きは、音のルーチンのコードと画面の更新のループの中で、`back` が選ぶ命令でだけ `hi` を 9,000 にクランプする（述語つきの `RoomLate.sclamp`）。ループを回る道はどれもそういう命令を通るので、`hi` は有界のままで、表は閉じる。述語はプログラムカウンタの ROM のバイトを読む。アドレスは並べない。ROM のデータのバイトが後ろへのジャンプに見えることもあるが、それは走らない場所で時間を求めるだけ。

**4 つの歩き.** (i) 制御 0 でバッファを知らない、(ii) パターン `L` から、(iii) パターン `L₆` から、(iv) 制御 6 でバッファを知らない。測った値（`buffer-ctl-check FM2 1 loopcheck`、ほかの仕事が 3 つ走っているとき）:

| 歩き | クランプ | 探索の状態 | 表 | 通らない状態 | アイドルループ以外の最大の `hi` | 時間 |
|---|---|---|---|---|---|---|
| (i) | `scrQ` | 254,954 | 141,625 | 0 | 56,670 | 73 秒 |
| (ii) | `sndQ` | 137,426 | 60,571 | 0 | 56,670 | 46 秒 |
| (iii) | `sndQ` | 725,638 | 325,399 | 0 | 56,886 | 232 秒 |
| (iv) | `scrQ` | 412,437 | 255,489 | 0 | 57,237 | 134 秒 |

最大の `hi` は 57,237 なので、どの道も `L` の 26,000 ドット前に終わる。ROM には音のルーチンのコードに後ろへのジャンプが 89、画面の更新のループに 2 ある（レコードのバイトの内側のループと、レコードのループ）。

**コスト.** ラウンド 29 の `recCheckT` は (i) と (iv) を `L` へのクランプで歩き、ネイティブで約 165 秒、非公開のファイル 1 つ（`Proof.SiteMusic`、約 180 秒）だった。`recCheckB` は 4 つとも時間つきで歩くので長くなる: ファイル 1 つでは 456 秒だった。そこで非公開の証明は 4 つの歩きを 4 つのファイル（`Proof.SiteMusic1` から `Proof.SiteMusic4`、`recCheckB_of`）で確かめ、lake はそれらを同時にビルドする: 最後の全体のビルドで 62 秒、37 秒、150 秒、102 秒。

**消す書き込み.** `writeAddr(m)` はポインタと Y の和（`RoomBlocks.writeAddr_eq`）。上のバイト `h` を知っていて `256 h + 510 < 2048` なら、ポインタは `256 h + 255` 以下、Y は 255 以下なので、アドレスは RAM の中で `256 h` 以上（`addr_page`。2 つのバイトからのポインタの値は、7 · 256 のポインタすべてで `decide` で確かめる、`ptr_val`）。測った値（`loopcheck 3`、歩き (i) と (ii) の表のすべての状態から）: 消すところで歩きは 6 つの状態に会い、どれも上のバイトを知っている。下のバイトや Y を知るものはない。ブロックのバッファを読むところ（18 状態）も同じ。歩きの `ADC` は両方の値のすべてのビットを知っているときだけ結果を出し、プレイヤーの位置は知らないので、行のオフセット（Y）と列（下のバイト）はわからない。

## 本物のフレームでの確かめ

`buffer-ctl-check FM2 1100 loopreal`: ムービーの部屋のフレームと、そこからの自分の走り（ランダムな入力、小さいマリオで 1,100 回、大きいマリオで 1,100 回、それぞれ 600 フレームまで）で、音のルーチンのコードの後ろへのジャンプと画面の更新のループの後ろへのジャンプの最大のドット。

| 走り | フレーム | 音のルーチンの後ろへのジャンプ（最大のドット） | 画面の更新のループの後ろへのジャンプ（最大のドット、走った数） |
|---|---|---|---|
| 部屋のムービー | 111 | 6,200 | 5,420（404） |
| 自分の走り、小さい | 578,997 | 6,784 | 6,008（884,680） |
| 自分の走り、大きい | 577,374 | 7,463 | 6,539（895,399） |

だから 2 つのフィールド（9,000）は測ったすべてのフレームで成り立つ。大きいマリオの走りで余裕は 1,537 ドット。

同じ走りで、フィールドのままの `SiteOK` の 3 つの部分も測った。消す書き込み（ムービー 13、小さい 4,802、大きい 5,541）はすべて 2 つのブロックのバッファの 1 つ目に入り、2 つ目の終わりから遠い。横の土管が x を読むところ（1、316、295 回）では x は 195 から 197 px。下の 4 ビットが 0 なのは 208 px だけ。ブロックのバッファの読み（728、1,973,613、1,972,449）で、バッファの外を読んだものも、表にないタイルを読んだものもなく、頭の読みで 0 とコイン以外を読んだものもない。

## 仮定（Lean で証明していない）

* フレーム `U` の **`roomLateU`**: 画面の更新のレコードのループと音のルーチンの後ろへのジャンプはドット 9,000 までに走る。画面の更新のループはレコードごとに 1 回、レコードのバイトごとに 1 回回る。歩きが知らないバッファからは回数がわからない。証明には前のフレームが書いたレコードが要る（ラウンド 28 は制御 6 からのフレームに終わりのクラスを試したが、歩きが終わらなかった）。
* ほかのフレームの **`roomLateS`**: 音のルーチンの後ろへのジャンプはドット 9,000 までに走る。証明には各フレームの始めの曲の状態が要る（ラウンド 6 は本物の走りで 207 の曲の状態を測った。音のルーチンのバイトがどんな値でもよいとするまとめは偽）。

## 再現

```
.lake/build/bin/smbrta buffer-ctl-check FM2 1 loopcheck     # 後ろへのジャンプで時間をクランプする 4 つの歩き、ネイティブ（2 は recCheckB も）、約 8 分
.lake/build/bin/smbrta buffer-ctl-check FM2 3 loopcheck     # 歩き (i) と (ii): タイルを読むところ、コインを消すところ、横の土管が x を読むところで歩きが知ること
.lake/build/bin/smbrta buffer-ctl-check FM2 1100 loopreal   # 本物のフレームでの後ろへのジャンプのドットと、read、erase、xbit の部分
```
