[← Back](README-ja.md) | [English](e-2-10-3-27-SideFacts.md) | [Japanese](e-2-10-3-27-SideFacts-ja.md)

# ルートでのパート f の 2 つのバイトの条件

第 36 回は、フィールド `sideW` を `SideAcross.FactsAt` のないフレームでだけ求めました（[フレームをまたいで残る 2 つのバイトと城の始めの行、横のタイマーに届きうる書き込み](e-2-10-3-26-SideAcross-ja.md)）。そしてルートのどのフレームもそれを持つことを、パート f のフィールドから証明しました（`SideAcross.Run.factsAll`）。しかしルートはその証明を使いませんでした。ここではルートがそれをパート e に渡し、フィールド `sideW` はなくなります。

**主張（第 37 回）.** 次のように書きます。

```
b, c        = ブロックのバッファの列（BlockBufferColumnPos）、ブロックのオブジェクトの位置（SprDataOffset_Ctrl）の RAM の位置
InvB(m)     := m[b] < 32 ∧ m[c] ∈ {0, 1}
MissB(m)    := m での添え字かポインタを通した書き込みは b も c も書かない
FactsAt(M)  := InvB(M) ∧ ∀ k, frame(trace M k) = frame(M) → MissB(trace M k)
K           = タッチのフレームまでのパート f の走りのフレーム（PoleJoin.Run.keep）: n < ix g の all n、inp n
```

1. `SideAcross.Run.factsK`: `PoleJoin.Run` の走り `R` について、パート f の ROM の確かめ（`poleCheckZ`、`keepCheckOf`、`bcolCheck`、`PoleNear.nCheck`）、操作を得たときの機械（`Start`、`fracCheck`、`AtCtl`）、操作を得たときの 2 つのバイトと地図（`PoleBcol.BInv`、`PoleTileKeep.watchB`、`PoleTileWalk.ColMap`）、2 組の RAM の位置が同じという 2 つの確かめ（`he1`、`he2`）から

```
∀ n < ix g,  FactsAt(all n)          （タッチのフレームまでのどのフレームも。数えるものも数えないものも）
```

   これはパート f のフィールド `bKeep`（`Run.bNoW` を通して）、`keepB`、`bufAll` での `SideAcross.factsAt_frames` です。`Run.factsAll`（数えるフレーム）はこれから出ます。
2. `SurfaceFrames.AreaRun` に新しい部分 `facts : ∀ n < ix g, FactsAt(all n)` があり、`OnFrames.areaRun` はそれを仮定 `hF` として受け取ります。
3. `OnFrames.sideWAt`（第 33 回の形のフィールド: 横のタイマーに届きうるすべての書き込みで）は、どのフレームでも 1 つの歩きになりました: `AreaRun.facts` とフィールド `castleRow` を使う `SideAcross.near_sideA` です。フィールド `sideW` はなくなりました。

変えた定理の公理: `propext`、`Classical.choice`、`Quot.sound`。ゲームのデータはありません: `b` と `c` は記号です。

**フィールド.** なくなったもの: `OnFrames.sideW`。新しいもの: なし。ルートはフィールドを増やしません: `hF` はルートの非公開の証明の中で `R.pole` から証明します（`SideAcross.Run.factsKM`: 箱を `⟨M, dx, dy, rows⟩` と書いた `Run.factsK`。`PoleJoin.touch_castle` と同じ書き方で、非公開の証明の機械についての事実が、それを展開せずに合います）。使うのは、すでにあった操作を得たときの条件（`PoleTileCtl.colMap₀`、`PoleTileCtl.watch₀`）と、もう 1 つ（`PoleParserRun.bInv₀`、すでにあった確かめ `pole_bcol_rows` で）と、2 つの確かめ `he1`、`he2`（ROM での `native_decide`）です。

**循環はない.** `factsAt_frames` が受け取るのは、パート f のフレーム `FrameKeep.Frames` とパート f のフィールドだけです。どれも `OnFrames` から証明しないので、`sideW` も `sideWAt` も使いません。`PoleBcol.frames_bcol`、`PoleTileKeep.frames_keepY`、`PoleNear.near_frames` も `OnFrames` を受け取りません。

**`hF` を受け取る定理.** `AreaRun` を作るどの定理も、それを使うどの定理も、`hF` を受け取り、先へ渡します:

- パート e: `OnFrames.areaRun`、`quiet_upto`、`surface_of_frames`
- パート f、`PoleJoin`: `Run.reads`、`Run.next`、`Run.moved`、`Run.stop_step`、`Run.stored_step`、`Run.inRange`、`hB_run`、`base_late`、`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle`
- パート f、`PoleParserRun`: `edgeLow_run`、`amount_run`、`invJ_run`、`inv_run`、`colMono_run`、`tilesCol_run`、`colEdge_run`、`tilesCol_route`

パート f の定理では `hF` は `hc0`（操作を得たときの機械）のすぐあとに、パート e の定理では `hst`（どのフレームも操作のある状態で始まる）のすぐあとに来ます。非公開の証明の `pole_join`、`pole_touch`、`pole_touch_castle` も受け取ります。

**確かめが 1 つ減る.** `numbersCheck` は `SideLoop.lCheck`（第 35 回の歩き、ネイティブで約 15 秒）を持っていました。`sideWAt` がそれを使うのは `FactsAt` のないフレームだけでした。それを外し、`Numbers.rangeC` と `AreaRun.rg` もなくしました。

**測ったこと.**

| 確かめ | 何を | 結果 |
|---|---|---|
| `surface-frames-check FM2 200` | `FactsAt` のないフレーム、`castleRow`、`sideWAt (a theorem)`、スクロールの止めが 0 でない、タイマーの止めが 0 でない状態で始まるフレーム（新しい測り） | 終了コード 0（1:10:35、564 MB）: 8 組、239,510 フレーム。失敗は 0（`castleRow`、`sideWAt (a theorem)`、測った第 36 回の `sideW`）。`FactsAt` のないフレームは 0。スクロールの止めが 0 でない状態で始まるフレームは 0、タイマーの止めが 0 でない状態で始まるものも 0。ほかの出力は第 36 回と同じ |
| `edge-real FM2 256` | 第 36 回と同じ | 終了コード 0（48:27）: 時間のほかは第 36 回と同じ出力 |
| `route-check`（TAS、1089 `02808080`、996 と第 23 回のジャンプの走り）、`up-clean-u`、`keep-frames-check 100`、`pos-keep-real 64`、`collide-real 200`、`pos-after-real 200` | 第 36 回と同じ | すべて終了コード 0。時間のほかは第 36 回と同じ出力 |

**城の始めの行（証明していない）.** フィールド `castleRow` は残ります。TAS と ROM で測ったこと:

- エリアのデータのポインタは、地上のすべてのフレームで 1 つの値です。地上のエリアのデータは、見出しのあとの 2 バイトのオブジェクトの並びで、終わりの印があります。その 1 つが城で、始めの行は `castleRow` の上限の中にあります。
- データの中の読み込みの位置（`AreaDataOffset` と `AreaObjOffsetBuffer` の 3 つ）は、TAS のどのフレームでも偶数です。城はタッチの前にオブジェクトの場所に読み込まれます。
- ROM では、データの偶数の位置（254 まで）のオブジェクトで、読み込みが城とみなすものの始めの行は高々 10 です。奇数の位置では、そうでないものが 1 つあります。

そのため、ポインタと、位置が偶数であることを知り、読み込みが位置を読むところで位置をその値に分ける歩きなら、読み込みがどのオブジェクトを解くかを知り、城の行を知ります。そのような歩きの 2 つの探索（証明の一部ではない）:

| 探索 | 結果 |
|---|---|
| 城のループでの分割をなくした `near_sideA` の歩きで、スクロールの処理の呼び出しでポインタと位置の 0 ビット目を知り、読み込みの 2 つの読みで位置をその値に分け、オブジェクトのルーチンで（0 ビット目のほかを）忘れるもの | 表の最初の 3,000 の状態で 39 の失敗: 敵のコードの、`X` を使うゼロページへの 4 つの書き込みでポインタを失う。そこで歩きは `X` を知らない（そこの表の状態の `X` は 0 から 255） |
| 同じもので、ポインタを守ったもの（添え字かポインタを通した書き込みがそれを書かないとして） | 表の最初の 3,000 の状態で失敗はない。しかし探索全体は 21 分で終わらず、5.8 GB を超えた（第 36 回の歩きは 17 秒） |

この方法で `castleRow` を証明するには、歩きに次が要ります: (1) ポインタが残ること: 添え字かポインタを通した書き込みがそれを書かない。歩きがそれを示せるのは、敵のコードで `X` の範囲を知るときだけです。(2) どのフレームの始まりでも位置が偶数で、フレームからフレームへ残ること（フレームの終わりでの歩きの状態）。(3) 値への分割よりずっと小さい探索。

**スクロールの止め、タイマーの止め、けがのタイマー（証明していない）.** `clampR` はスクロールの止めが 0、`Moves.stop` の場合 B はタイマーの止めが 0、`endKeep` の位置のバイトはけがのタイマーが 0 であることを、ルートが着くフレームで要します。第 36 回の歩きでは、スクロールの処理のあと、添え字かポインタを通した書き込みで、スクロールの止めを書きうるものはなく、タイマーの止めには 1 つ（`RenderUnderPart` の背景のループ）、けがのタイマーには `X` を使う敵の書き込みが 12 あります。プログラムはそれぞれをアドレスでも書きます: スクロールの止めは、スクロールの止めのエリアのオブジェクト（エリアのデータだけがそれを選ぶ）、画面の下に落ちたとき、旗のポールで。タイマーの止めは、けがをしたときと死んだとき（同じフレームでルーチンも書くので、`FrameKeep.Frames.noStore` がタッチのフレームより前ではそれを除く）で、数え下げは 0 でない値からだけです。証明には、操作を得たときのそれぞれのバイトと、フレームの始まりから終わりまでその値を知る歩きと、スクロールの止めには上のエリアのデータが要ります。`surface-frames-check FM2 200` の 239,510 フレームで、スクロールの止めかタイマーの止めが 0 でない状態で始まるフレームはありません。

**ここで証明していないこと.**

- `castleRow`（上）。
- `FactsAt` は仮定であるパート f のフィールド `bKeep`、`keepB`、`bufAll` によります。

**ファイル:** 変えたもの: `Theorems/SideAcrossRun.lean`（`Run.factsK`、`Run.factsKM`。`Run.factsAll` は `Run.factsK` から）、`Theorems/SurfaceFrames.lean`（`AreaRun.facts`、`OnFrames.areaRun`、`OnFrames.sideWAt`、なくしたフィールド `sideW`、`SideLoop.lCheck` のない `numbersCheck`、`quiet_upto`、`surface_of_frames`、`movesScan` の 2 つの測り）、`Theorems/SideAcross.lean`（1 文）、`Theorems/PoleJoin.lean` と `Theorems/PoleParserRun.lean`（上の定理の `hF`）、`Main.lean`（非公開の証明: `pole_join`、`pole_touch`、`pole_touch_castle` の `hF`、ルートの `have hFa`、`Theorems.SideAcrossRun` の読み込み。`surface-frames-check` の 2 つの数え）。
