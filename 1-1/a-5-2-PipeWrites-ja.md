[← Back](README-ja.md) | [English](a-5-2-PipeWrites.md) | [Japanese](a-5-2-PipeWrites-ja.md)

# 1 フレーム全部: ルーチンのバイトを書く命令

**主張.** 操作できる状態で始まるフレームを、抽象機械で最初から最後まで追います。ルーチンのバイトが土管の値になるフレームでは、その書き込みより前に右足で `BlockBufferCollision` に入っていて、そのときの位置は土管の範囲の左端より左ではありません。[前のページ](a-5-1-PipeEntryRule-ja.md) の `Pass` と `RowOK` は、もう仮定しません。残る仮定は 3 つです。フレームの始まりの状態 `FrameStart`、命令ごとの条件 `Clean`、タイルの条件 `TilesOK` です。全部 1 つの状態についての条件です。

名前は [前のページ](a-5-1-PipeEntryRule-ja.md) と同じです。`tr(n)` はフレームの `n` 命令あとの機械です。`rt` は `GameEngineSubroutine`、`e_v` は土管のルーチンの番号です。`S` は足の判定のときのスタックポインタです。

```
Prot            :=  {rt, OperMode, OperMode_Task, 足の加算の番号のバイト} ∪ スタックの上の部分 [0x100 + S − 32, 0x1FF]
Plain(t)        :=  (t が RAM ∧ t の RAM の場所 ∉ Prot)  ∨  (0x4000 ≤ t ∧ t は DMA でもパッドでもない)
target(m)       :=  m の命令が書き込む番地（下の命令について）

Clean(m)        :=  store:  m の命令が STA/STY zp,X、DEC/INC zp,X、STA abs,X、DEC/INC/ROR abs,X、STA abs,Y、STA (zp),Y なら  Plain(target(m))
                    read:   m の命令が LDA (zp),Y なら  読む番地は RAM か ROM
                    jump:   pc(m) = JumpEngine なら  A(m) < その表の長さ
                    time:   pc(m) ≠ EndlessLoop なら  dot(m) ≤ dotsPerFrame − 64

FrameStart(m)   :=  pc(m) = EndlessLoop  ∧  スタックポインタはそこの値
                    ∧  (dot = 0 ∧ vblank なし ∧ NMI なし  ∨  1 ≤ dot ≤ 9 ∧ vblank ∧ NMI)
                    ∧  PPUCTRL のビット 7 が 1  ∧  ストローブなし  ∧  sprite-0 のフラグは dot のとおり  ∧  止まっていない
                    ∧  rt = 操作のルーチン  ∧  OperMode = ゲーム  ∧  OperMode_Task = ゲームコア

HypG(m)         :=  (AtEntry(m) → px(m) < L_px)  ∧  (AtRead(m) → TilesOK(m))      （右足で分けるとき。移動の終わりで分けるときは項目 1-1-a-5-9）
TilesAll(m)     :=  ∀ ブロックバッファの場所 d,  mem(d) = T_R  →  d = d_R  ∧  pg ≤ page(m) + 1
```

表の長さはプログラムが ROM から数えます。`JSR JumpEngine` のあとの 2 バイトずつを、ROM を指さない語か、それまでの語が指す番地に来るまで数えます。

```
no_write_frame      :  frameCheck,  s(j + 1) = step(s(j)) (j ≤ n),  frame(s(j)) ≤ frame(s(0)) (j ≤ n),  FrameStart(s(0)),
                       (∀ j ≤ n,  Clean(s(j)) ∧ HypG(s(j)))                         →  rt(s(n + 1)) ≠ e_v
entry_right_of_left :  ruleCheckG,  Enters(m, i),  FrameStart(m),
                       (∀ n,  WriteStep(n) → ∀ j ≤ n,  Clean(tr(j)) ∧ (AtRead(tr(j)) → TilesOK(tr(j))))
                       →  ∃ n j,  WriteStep(n) ∧ j ≤ n ∧ AtEntry(tr(j)) ∧ L_px ≤ px(tr(j))
rule_on_frames      :  ruleCheckG,  ∀ t,  Enters(fm t, inp t) → FrameStart(fm t),  Clean と TilesOK は上のとおり,
                       (P₂(t) は右足のときの位置: P₂(t) = 256·px(tr(j)) + f,  0 ≤ f,  j ≤ n)
                       →  ∀ t,  Enters(fm t, inp t)  →  L ≤ P₂(t)
tiles_of_steps      :  TilesAll(s(0)),  (∀ k < N,  TileStep(s(k), s(k + 1)))         →  ∀ k ≤ N,  TilesOK(s(k))
pipe_frame_check（非公開）   :  ruleCheckS(sy, m₀) = true（native_decide。移動の終わりで分ける抽象機械、項目 1-1-a-5-9）
pipe_no_entry_real（非公開） :  Enters(fm E, inp E),  FrameStart(fm E),  clean, tiles, edge, moved,  openP, openB,  機械から読むフレーム（[次の項目](a-5-5-PipeFrames-ja.md)）  →  367 < E
```

ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/PipeWrites.lean`、非公開の `Proof/PipeWrites.lean`。

## しくみ

**抽象機械.** [`TaintRun`](b-2-3-TaintRun-ja.md) の機械です。わかっているのは `rt`、`OperMode`、`OperMode_Task` の 3 バイトと、`PPUCTRL` のビット 7、スタックポインタだけです。ほかの RAM、レジスタ、パッドはわかりません。

**機械に足した歩き方.** どれも `Sim` を保つと証明しました。`TaintRun` は変えていません。

* 添字かポインタで番地がわからない書き込み。`Plain` のおかげで `Prot` は変わりません。ほかの RAM は全部わからなくします（`forgetW`）。
  `TaintRun` のカウンタとして追うバイトは、`Prot` にあれば追い続けます（`AS.forgetK`）。この歩きにカウンタはありませんが、[数えないフレーム](a-5-5-3-LagFrames-ja.md) が使います。
* ポインタがわからない `LDA (zp),Y`。読む番地がレジスタでないので、機械は変わりません。読んだ値はわかりません。
* `ADC abs,Y`。`A` の上の 4 ビットがわかり、足す値が下の 4 ビットを持たず、キャリーが 0 のとき、和の上の 4 ビットがわかります。

**分ける場所（`preG`）.** どれも機械の変更ではありません。

* 時間: `time` のとおり、窓の上端を切ります。
* `JumpEngine`: `jump` のとおり、`A` を表の番号ごとに分けます。
* `DoFootCheck`: 縦の位置を上のビットで分けます。`CMP` で下に行きすぎるものは足の判定を出ます。
* 右足で縦の位置を読むところ: 上の 4 ビットで分けます。ですから読むときの `Y` は 1 つの値です。`RowOK` はいりません。
* 右足の入口: 仮定 `px < L_px` のもとで位置の値ごとに分けます。ページの数は高々 `pg + 1` です。
* 右足の読み: ポインタと `Y` がわかるので、読むバイトの場所がわかります。そこがブロックバッファの中で `d_R` でないか、まだタイルがないなら、`TilesOK` で「`T_R` のあるビットと違う」に分けます。

**確かめること（`walkG`）.** 全部の道で、次の状態の `rt` が `e_v` でないこと。`HandlePipeEntry` の `CMP` が足のビットを見るので、`w` に行く道はありません。ほかの直接の書き込みは、わかっている値を書きます。そのあとも `rt` のビットを 1 つ保ったままフレームの終わりまで追います。

**探索（証明の外）.** 衝突ルーチンの外では、スタックとルーチンのバイトが同じ状態を 1 つにまとめます。

**大きさ.** 1,504,949 ステップ、166,506 の枝分かれ、失敗 0、表 57,015、通った命令 8,169。番地がわからない書き込みは 496 か所、ポインタがわからない読みは 40 か所です。プログラムで約 4 秒です。

## 本物のフレームで確かめたこと

プログラムです（`pipe-rule-check`）。条件は、操作できる状態で始まるフレームの全部の命令で確かめました。入るフレームだけではありません。

| 走り | フレーム | 操作で始まる | 命令 | 入ったフレーム |
|---|---|---|---|---|
| TAS の入るまで | 368 | 368 | 1,917,255 | 1 |
| TAS の入ったあと | 1,300 | 351 | 1,635,098 | 0 |
| 入る前の状態から歩いて下 | 5,480 | 5,480 | 27,774,369 | 161 |
| 入る前の状態から跳んで、下を押して着地（大きいマリオに書き換えたものを含む） | 25,308 | 24,161 | 145,324,806 | 14 |
| 入る前の状態から乱数の入力 | 26,855 | 26,295 | 130,905,665 | 1 |
| 同じ。大きいマリオに書き換え | 9,000 | 8,570 | 43,271,021 | 0 |

* どの行でも、`FrameStart` を満たさないフレームは 0、`Clean` を満たさない命令は 0、`TilesOK` を満たさない右足の読みは 0 です。
* 入った 177 フレームは全部 `w` で書きます。位置は範囲の 9 個の値全部に出ます。範囲の外はありません。右足の入口の位置は書き込みまで 1 つの値で、フレームの終わりまで変わりません。
* 書き込みの dot は高々 25,622 です。操作のフレームの命令の dot は高々 69,101 です。
* 操作できる状態になったとき、ブロックバッファに `T_R` はありません。添字かポインタで `T_R` を書く命令は全部で 91 回あります。全部 `d_R` に書き、そのときページは `pg − 1` 以上です。`T_R` があるあいだ、ページが `pg − 1` より小さくなることはありません。
* `Clean` の `store` は、操作のフレームの外では成り立ちません。RAM を消す `InitializeMemory` は `rt` を書きます。操作のフレームでも、添字の書き込みはスタックのページの下の部分に届きます。ですから `Prot` はスタックの上の部分だけです。

## 前提（Lean では証明していない）

* **`FrameStart`（項目 1-1-a-5-2-1）** は、もう `Route.Pipe` のフィールドではありません。入るフレームはアイドルループで、操作できる状態で始まります。これは操作から入るまでの全部のフレームについての帰納法で証明しました（[操作から土管までの各フレームはアイドルループで始まる](a-5-5-3-2-StartRun-ja.md)、`Pipe.startE`）。`rule_on_frameS` はフレーム `E` 1 つでの規則です。
* **`Clean`（項目 1-1-a-5-2-2）.** 書き込みまでの各命令について上の 4 つ。添字とポインタの範囲が要る場所は、これで 1 つの条件にまとまりました。添字が小さいことからの証明はしていません。`time` はフレームの最後の 64 dot についてです。
* **`TilesOK`（項目 1-1-a-5-3）.** `tiles_of_steps` は、これを 1 命令ずつの条件 `TileStep` にします。`Route` は使っていません。`T_R` がブロックバッファに入るのは面の読み込みからです。面の読み込みのバイトは追っていません。
* **`pos`（項目 1-1-a-5-9）** は、もう仮定しません。抽象機械は位置を移動の終わりで分けるようになりました: [移動の終わりの位置](a-5-9-MoveEnd-ja.md)。かわりは `moved`（`P₂` は移動の終わりの位置）と `edge` です。
* **範囲の右端.** ここでは左端だけを出します。`Route` が使うのは左端だけです。

**ファイル.** `Theorems/PipeWrites.lean`、非公開の `Proof/PipeWrites.lean`。`Theorems/PipeEntryRule.lean` の定義を使います。記号 `JumpEngine`、`EndlessLoop` を足しました。

**再現.**
```
.lake/build/bin/smbrta pipe-rule-check FM2    # 1 フレームの確認と、本物のフレームでの仮定、約 2 分
```
