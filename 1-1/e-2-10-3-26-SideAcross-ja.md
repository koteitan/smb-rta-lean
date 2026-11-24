[← Back](README-ja.md) | [English](e-2-10-3-26-SideAcross.md) | [Japanese](e-2-10-3-26-SideAcross-ja.md)

# フレームをまたいで残る 2 つのバイトと城の始めの行、横のタイマーに届きうる書き込み

ラウンド 35 は、フィールド `sideW` を 4 つの書き込みでだけ求めました（[エリアの読み込みのループの、横のタイマーに届きうる書き込み](e-2-10-3-25-SideLoop-ja.md)）: エリアの読み込みがブロックのバッファのポインタを通して書くもの、頭がブロックに当たるときにポインタを通して書く 2 つ、城の行のループの書き込みです。はじめの 3 つは、フレームをまたいで残る 2 つのバイトを必要とし、4 つ目は城の始めの行を必要とします。ここでは、パート f のそのバイトについての条件が成り立つどのフレームでも、歩きがその 2 つのバイトを知り、始めの行は 1 つの命令の上の条件から知ります。だから `sideW` はほかのフレームでだけ求め、その城の部分は始めの行についての新しいフィールド `castleRow` になります。

**主張（ラウンド 36）.** 次のように書きます。

```
s, b, c     = 横のタイマー、ブロックのバッファの列（BlockBufferColumnPos）、ブロックのオブジェクトの位置（SprDataOffset_Ctrl）、RAM の番号として
SideW(m)    := m での添え字かポインタを通した書き込みは s を書かない
NearW(m)    := ラウンド 33（絶対アドレスに X か Y を足した書き込みで、ある添え字が元のアドレスから s に届くもの、または STA (zp),Y）
InvB(m)     := m[b] < 32 ∧ m[c] ∈ {0, 1}
MissB(m)    := m での添え字かポインタを通した書き込みは b も c も書かない
FactsAt(M)  := InvB(M) ∧ ∀ k, frame(trace M k) = frame(M) → MissB(trace M k)          （M のフレーム: その始まりと、その各命令で）
CastleRow(m):= pc(m) = CRendLoop → X(m) ≤ 10              （城の行のループの頭で、行は高々 10）
```

`SideAcross.near_sideA`: `SideLoop.near_side` の仮定（アイドルループで始まり、各命令が `FrameKeep.guardE` の `CleanK` を満たし、ルーチン、モード、タスクをアドレスで書く命令がなく、n₀ でプレイヤーのルーチンに来る）と、`FactsAt(M)` と、スクロールの処理の呼び出しからの各命令での `CastleRow` を持つ制御中のフレームをとります。するとそれは n₀ より後の最初の kq でスクロールの処理の呼び出しに来て、

```
フレームの中のすべての j ≥ kq で:  NearW(trace j)  →  SideW(trace j)
```

ROM の上の確かめは `aCheck`（歩き）と `keepCheckA`（フレームの始まりからスクロールの処理の呼び出しまでの 2 つのバイト）です。公理: `propext`、`Classical.choice`、`Quot.sound`。ゲームのデータはありません: 2 つのバイトとループの頭は記号です（`BlockBufferColumnPos`、`SprDataOffset_Ctrl`、`CRendLoop`、どれもラウンド 35 から `tools/smb-symbols.txt` にある）。`0x91` は 6502 の `STA (zp),Y` の命令の番号です。

**なぜ `FactsAt` か.** どちらのバイトも、1 つのフレームの歩きが知る限りでは、1 つのフレームだけでは保たれません:

- ブロックのバッファの列: コインを消すときと、ブロックのオブジェクトを書きかえるときのブロックのバッファのポインタを通した書き込みは、歩きの知らない下のバイトと行を持ち（足し算と、フレームをまたいで残るバイトから来る）、その範囲は列の場所に届きます。コードを読むと、1 つの道筋がそれを書きえます: 頭がブロックに当たるときに、バッファの最後の行の次の行を固いブロックと見たら（画面の下の近くで上に動いていなければならない）、ブロックのオブジェクトの書きかえが、あとで列の場所にメタタイルを書きます。測った本当の走りでは起きません;
- ブロックのオブジェクトの位置: 画面のバッファへの `Y` を通した書き込み（画面のバッファ自身の位置で、フレームをまたいで残る）がそこに届きえて、敵の `X` を通した書き込みも届きえます。

パート f は、添え字かポインタを通した書き込みがそれを書かないことを仮定し（`PoleJoin.Run` のフィールド `bKeep`、`PoleBcol.BcR` と、`keepB`、`PoleTileKeep.KeepB`。パート f のラウンド 36 から `bKeep` は `PoleNear.near_frames` が残すところでだけ求め、`PoleJoin.Run.bNoW` が、解析の書き込みを除くフレームの各命令で列の部分を与え、その書き込みでは `frames_bcol` が与える）、それと制御のときの値から、各フレームが `InvB` で始まることを証明します（`PoleBcol.frames_bcol`: 列は読み込みの列を 32 で割った余り。`PoleTileKeep.frames_keepY`: 位置のビット 1 から 7 は 0 のまま）。それはルートのすべてのフレームでの `FactsAt` です: `SideAcross.Run.factsAll`（ファイル `Theorems/SideAcrossRun.lean`）。2 組の番号（ここの記号と、パート f がコードから読む命令の引数）が同じという 2 つの確かめがつきます。

**歩き.** ラウンド 35 の歩き（`SideLoop` の鍵と分けを持つ `SideRange.walkR`）に、4 つの変更を加えます:

1. その守り（`guardA`）は、b と c を守る `FrameKeep.guardE` です: その `CleanK` は `guardE` の `CleanK` と `MissB` から来ます（`cleanK_A`）;
2. スクロールの処理の呼び出しで、ラウンド 35 の状態に、b が 32 より小さいことと c が 0 か 1 であることを知らせて始めます（`setB`）。そこの 2 つのバイトはフレームの始まりのものです: プレイヤーのルーチンまで 1 つのバイトを追う `CtrlKeep` の歩きと、そこからスクロールの処理までの `PlaceKeep` の歩きを、b と c のそれぞれについて（`keepCheckA`、`keep_cutA`、`keep_subsA`、`SideTimer.keep_at` と `PlaceKeep.keep_place` のように）;
3. 下のバイトを知らないポインタを通した書き込みのあとで、ゼロページの各バイトのうち、ポインタの上のバイトと `Y` の範囲から、どの書き先もはずれるものを取り戻します（`takeP`、`fixP`。`izy_locs`: そのような書き込みは書き先だけを書き、`SideRange.missP` は書き先がそのバイトをはずれると言う）。前は、そのような書き込みで歩きはゼロページを忘れ、ポインタも忘れました;
4. 城のループの頭で、`X` を行 0 から 10 に分けます（`spC`）。この分けは `CastleRow` を満たす機械だけをおおうので（`cov_spC`）、歩きの補題は各命令の上の条件 `H` をとります（`CovH`、`live_stepP`、`okP_all`）。

b が 32 より小さいと、エリアの読み込みのポインタはブロックのバッファを指します。c が高々 1 だと、頭がブロックに当たるときの `X` を通したゼロページへの書き込みは 2 つの正確な片に分かれ、どれもポインタを書きません。3 つ目の変更で、ポインタは読み込みの行のループを通して、また頭の 1 つ目のポインタの書き込みから 2 つ目まで、知られたままです。4 つ目で、城のループは行 0 から 10 だけを書きます。

**ルートでは.** `OnFrames` のフィールド `sideW` は `FactsAt` のないフレームでだけ求め、新しいフィールド `castleRow` が城のループでそのかわりをします:

```
sideW     : ∀ j, 1 ≤ j → j < g → side(seq j) ≠ t₁₆ →
              ∀ k n, arrAt ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → NearW(trace n) → Resid(trace n) →
                ¬FactsAt(fm j) → SideW(trace n)
castleRow : ∀ j, 1 ≤ j → j < g → side(seq j) ≠ t₁₆ →
              ∀ k n, arrAt ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → CastleRow(trace n)
```

`Resid` はラウンド 35 の `SideLoop.Resid`（4 つの書き込み）です。`OnFrames.sideWAt`（ラウンド 33 のフィールド）は、`FactsAt` のあるフレームで `near_sideA`（`castleRow` とともに）を、ないフレームで `Resid` の外の `SideLoop.near_side` と `Resid` でのフィールドを使います。`numbersCheck` は確かめを 1 つ多く持ちます: `SideAcross.check` = `aCheck` と `keepCheckA`（`Numbers.acrossC`、`AreaRun.ac`）。

- `sideW` はラウンド 35 のフィールドより少なく求めます: 同じフレームと書き込みですが、`FactsAt` のないフレームでだけで、パート f のフィールドはルートにそのようなフレームを残しません（`Run.factsAll`）。ルートはまだ `Run.factsAll` を使いません: `SurfaceFrames.AreaRun` を受けとるルートの定理が、制御のときの値を仮定として、パート f のファイルで必要とします。
- `castleRow` は新しいものです。`sideW` が求めたのと同じフレームと同じ命令から求めますが、ループの頭で、書き込みの書き先のかわりに行を求めます。ラウンド 35 のフィールドの城の部分より弱くはありません: ループが行 11 以上から始まり、フレームの終わりまでにタイマーに届かない機械では、ラウンド 35 のフィールドは成り立ち、`castleRow` は成り立ちません。プログラムでは、そのときループはフレームの中でページ全体を回り、タイマーに届きます。

**測ったもの.**

| 確かめ | 何を | 結果 |
|---|---|---|
| ネイティブの探索（`SideAcross.aFails`） | スクロールの処理の呼び出しからの歩きの探索 | 失敗 0。たどった状態 53,298、表の状態 45,200 |
| ネイティブの評価 | 1-1 のエリアの種類での `aCheck`、`keepCheckA` | 約 17 秒と 1.5 秒で true（ラウンド 35 の `lCheck`: 同じ負荷で約 15 秒） |
| ネイティブの下書きの探索 | 城のループで分けず、そのループを除いた歩き | そのループのほかは失敗 0（そこで 36） |
| ネイティブの下書きの探索 | b と c を知るが守らない歩き | ラウンド 35 と同じ 3 つの失敗の場所（2 つのバイトは、コインを消すところと画面のバッファの書き込みで失われる） |
| ネイティブの下書きの探索 | b と c を守って知るが、3 つ目の変更のない歩き | 読み込みの書き込みと、頭の 2 つ目のポインタの書き込みで失敗 |
| ネイティブの下書きの探索 | `aCheck` と同じで、ラウンド 34 の鍵と分け | 4 つの場所で失敗 125（メタタイルのバッファのループ） |
| ネイティブの下書きの探索 | この歩きで、スクロールの処理のあとのほかのバイトについて | 場所のバイトとスクロールのロック: それを書きうる書き込みはない。タイマーの制御: 1 つの書き込み、`RenderUnderPart` の背景のループ。けがのタイマー: 敵の `X` を通した 12 の書き込み |
| ネイティブの評価 | 2 組の番号（`factsAt_frames` の `he1`、`he2`） | 同じ |
| `surface-frames-check FM2 200` | `sideW`（狭めたフィールド）、`castleRow`、`sideWAt (a theorem)`、`FactsAt` のないフレーム（測るだけ） | どれも失敗 0。8 つの組、239,510 フレーム、確かめたもの 215,433、書きかえた状態を含む。どの組でも `FactsAt` のないフレームは 0。ラウンド 35 の `Resid` の書き込みに来るフレームは 2,239（ラウンド 35 と同じ） |
| `edge-real FM2 256` | `sideW`、`castleRow`、`sideWAt (a theorem)` | 失敗 0。出力はラウンド 35 と同じ（きれいに始まらないフレームでの古い覚えている速さと `after` だけで失敗し、数はラウンド 30 から 35 と同じ） |

**ここで証明していないこと.**

- `castleRow`。始めの行は、エリアのデータの城のオブジェクトの 2 つ目のバイトの下の 4 ビットです。それを証明するには、歩きが、フレームをまたいで残るエリアのデータのポインタと、読み込みのデータの中の位置と、1-1 の城のオブジェクトの行を知らなければなりません。
- ルートでの `FactsAt`: それは仮定であるパート f のフィールド `bKeep` と `keepB` から来ます（`Run.factsAll`）が、ルートはまだそれを使いません。 第 37 回: ルートはそれを使い、`sideW` はなくなりました（[ルートでのパート f の 2 つのバイトの条件](e-2-10-3-27-SideFacts-ja.md)）。

**ファイル:** `Theorems/SideAcross.lean`（`bcpI`、`sdoI`、`InvB`、`MissB`、`FactsAt`、`CastleRow`、`spC`、`CovH`、`cov_spC`、`guardA`、`cleanK_A`、`setB`、`sim_setB`、`missP_ne`、`izy_locs`、`takeP`、`fixP`、`fixP_sim`、`sideW_of_missK`、`okA`、`okA_spec`、`walkP`、`live_stepP`、`okP_all`、`searchA`、`aCfg`、`aCheck`、`keepCheckA`、`check`、`keep_cutA`、`keep_subsA`、`near_sideA`）、`Theorems/SideAcrossRun.lean`（`factsAt_frames`、`Run.factsAll`）。変えたもの: `Theorems/SurfaceFrames.lean`（フィールド `sideW` と `castleRow`、`OnFrames.sideWAt`、`numbersCheck`、`Numbers.acrossC`、`AreaRun.ac`、`movesScan`）、`Main.lean`（`surface-frames-check` の数え）。
