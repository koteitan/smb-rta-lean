[← Back](README-ja.md) | [English](d-2-4-ScreenPage.md) | [Japanese](d-2-4-ScreenPage-ja.md)

# 部屋の画面のページと、横の土管の長いタイマー

**主張.** これは部分的な結果です。部屋で最初に操作できるフレームの状態が 1 つの条件 `Room` を満たし、そこから入るまでの各フレームの各命令が条件 `SiteOK` を満たし、入るまでの各フレームがプレイヤーのルーチンで始まるとします。このとき、入るまでのどのフレームでも画面は最初のページにあり、スクロールロックはオンです。入るフレームの終わりのタイマーは長い値で、160 以上です。証明は部屋の 1 フレーム全部を抽象機械で追います。フレームの部分には分けません。`Room`、`SiteOK`、ルーチンの条件は仮定です。本物のフレームで確かめました。

`m₀` は 1-1 の開始の機械です。`r` は参照の機械で、本物の走りの入る 1 フレーム前です（[横の土管から地上への切り替え](d-1-SideTransition-ja.md) の `P`）。`frame(m, i)` は入力 `i` の本物の 1 フレームです。`tr(n)` はそのフレームの `n` 命令あとの機械です。`page(m)` は `ScreenLeft_PageLoc`、`lock(m)` は `ScrollLock`、`rt(m)` は `GameEngineSubroutine`、`timer(m)` は `ChangeAreaTimer`、`x(m)` は `Player_X_Position` です。`e_s` は横の土管のルーチンの番号、`long` は `AreaChangeTimerData` のはじめの値です。`L` はフレームの終わりの 6000 ドット前です。

```
Room(m)     :=  m はアイドルループでフレームを終えている: pc と S は r と同じ、ドット ≤ 9、
                vblank と NMI のフラグはドットに合う、スプライト 0 のフラグは立つ、PPU 制御で NMI はオン、ストローブなし
                ∧  ∀ (b, k) ∈ K,  m[b] & k = r[b] & k

SiteOK(m)   :=  ( pc(m) ≠ アイドルループ          →  dot(m) ≤ L )
              ∧ ( m の命令が LDA (zp),Y            →  読む番地は RAM か ROM )
              ∧ ( pc(m) = ブロックバッファの読み   →  読むバイト ∈ T )
              ∧ ( 同じ場所で、足し算の番号が頭     →  読むバイト ∈ {0, コイン} )
              ∧ ( pc(m) = コインを消す書き込み     →  書く番地はブロックバッファの中 )
              ∧ ( pc(m) ∈ 画面のバッファの 3 か所  →  VRAM_Buffer1_Offset < 64 )
              ∧ ( pc(m) = 土管のコードの x の読み  →  x(m) & 15 ≠ 0 )

Leaves(m')  :=  page(m') = page(r) ∧ lock(m') = lock(r) ∧ rt(m') ≠ rt(r) ∧ ( rt(m') = e_s → timer(m') = long )
```

`K` は 73 バイトの既知のビットです。下に挙げます。`T` は `r` のブロックバッファにあるタイルと 0 です。

```
room_step    :  Room(m) ∧ (∀ j, SiteOK(tr(j)))  →  Room(frame(m, i)) ∨ Leaves(frame(m, i))
room_run     :  seq(n + 1) = frame(seq(n), inp(n)),  c ≤ e,  Room(seq(c)),
                ∀ n ∈ [c, e),  (∀ j, SiteOK(tr_n(j))) ∧ rt(seq(n)) = rt(r),   rt(seq(e)) = e_s
                →  (∀ n ∈ [c, e), Room(seq(n)))  ∧  timer(seq(e)) = long  ∧  page(seq(e)) = page(r)  ∧  lock(seq(e)) = lock(r)
room_keeps   :  Room(m) ∧ (∀ j, SiteOK(tr(j)))  →  page(frame(m, i)) = page(m)  ∧  lock(frame(m, i)) = lock(m)
RoomRun.screen :  同じ仮定  →  ∀ n ∈ [c, e],  page(seq(n)) = 0  ∧  lock(seq(n)) ≠ 0
RoomRun.timer  :  同じ仮定  →  160 ≤ timer(seq(e))
entry_long   :  同じ仮定（rt(seq(e)) = e_s のかわりに、タイマーのない入るときの条件）  →  タイマー 160 以上を含む入るときの条件
screen_check（非公開）: roomCheck(sy, nm, m₀, 160) = true（native_decide）
```

Lean: `Theorems/ScreenPage.lean`（`readStep`、`writeStep`、`s_readStep`、`s_writeStep`、`SiteOK`、`walkS`、`frame_of_walkS`、`RoomCond`、`Leaves`、`room_step`、`room_keeps`、`room_run`、`RoomRun`、`RoomRun.screen`、`RoomRun.timer`、`entry_long`）、非公開の `Proof/ScreenPage.lean`（`screen_check`、`screen_first_page`、`screen_long_timer`、`screen_entry`）。ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

## この項目の 3 つのこと

**(1) 入るフレーム.** 1 フレーム全部の確認の中に入っています。フレームの終わりの抽象状態が `rt = e_s` なら、その状態で `timer` は `long` と決まっていなければ確認は失敗します。土管のコードで `page` が 0 と知られているので、タイマーを書く枝は 1 つです。

**(2) 1 フレームで保つこと.** `K` はページとロックを全部のビットで含みます。`room_step` の両方の場合で値は変わりません（`room_keeps`）。ロックをオフにした状態、ページを 1 にした状態を参照にすると確認は通りません（下の表）。

**(3) 始まり.** 1 つの状態の条件 `Room(seq(c))` のままです。部屋に入る切り替えの段からは出していません（下の「前提」）。

## しくみ

**抽象機械.** [一部のバイトがわからない走り](b-2-3-TaintRun-ja.md) の機械をそのまま使います。新しくした部分はありません。その上に、3 つの歩き方を足しました。どれも 1 命令ぶんを本物の `step` に対して証明します。

* `LDA (zp),Y` でポインタがわからないとき（`readStep`、`s_readStep`）。読む番地が RAM か ROM なら、機械はほかに何も変わりません。読んだ値はわからないとします。ブロックバッファの読みでは、値を `T` の各値に分けます。
* `STA (zp),Y` でコインを消すとき（`writeStep`、`s_writeStep`）。ブロックバッファに既知のビットがないので、どこに書いても抽象状態は変わりません。
* 分けること（`preS`）。`dot ≤ L` で時間の幅を切ります。画面のバッファの添字は 64 未満の値に分けます。`x` は低い 4 ビットのどれかが立っている 4 つに分けます。

**表.** 探索が抽象状態の表を作ります。確認は表の各状態から歩き、どの道も表の状態に入るか、フレームの終わりで `Room` か `Leaves` になることを確かめます（`walkS`、`finR`）。探索が忘れるものは、確認が `AS.le` で確かめます。ですから探索は証明の一部ではありません。

**大きさ.** 探索 211,005 ステップ、8,767 の枝分かれ、失敗 0、表 9,383 個。プログラムで確認全体が約 4 秒、非公開の証明のビルドで約 9 秒です。

**1 フレームが閉じた理由.** 前の測定（[縦の土管に入るフレームを本物のフレームで](a-5-1-PipeEntryRule-ja.md)）で、パッドだけわからなくても失敗 179 でした。失敗の場所はポインタの読み、ジャンプ表、時間です。ここでは次の 4 つで閉じました。

* わからないポインタの読みを許す規則。条件は「レジスタを読まない」だけです。
* 読むタイルの値を分ける。旗竿、ツタ、斧、バネへの道が消えます。
* 頭の読みは 0 かコインだけ。レンガをたたく道が消えます。
* 物のバイトなどの `K`。

**ページとロックを書く命令**（ディスアセンブリから数えました）。ゼロページの添字つきの書き込み 338 個は届きません。

| 書き方 | ページ | ロック | 歩きが通った命令 |
|---|---|---|---|
| 直接 | 3 | 5 | ページ: なし。ロック: `PlayerHole` の 1 個。ここは 1 を書くので値は変わりません |
| 絶対番地の添字つき（439 個のうち届くもの） | 31 | 31 | 6 個（スプライトの番号 4 個、ジョイパッド 2 個）。どれも添字がわかっていて届きません |
| ポインタ経由 | 9 | 9 | 1 個（コインを消す）。ブロックバッファの中です |

歩きは 2,668 個の命令を通ります。`ScrollScreen`、`StartPage`、`ExecGameLoopback`、`ScrollLockObject`、`PlayerEndLevel`、`WarpZoneObject`、`FlagpoleCollision` は通りません。

## 条件を外すとどうなるか（測定）

プログラムで測りました。定理ではありません。

| 外した条件 | ステップ | 失敗 | 最初の失敗、結果 |
|---|---|---|---|
| なし | 211,005 | 0 | |
| `dot ≤ L` | 12,248 | 296 | `OutputToVRAM`。時間がフレームの終わりに届く |
| 頭の読みは 0 かコイン | 214,032 | 4 | `DBlockSte`。レンガをたたく道 |
| 読むタイル（どのバイトでも） | 400,000 で打ち切り | 116 以上 | `DBlockSte` |
| `VRAM_Buffer1_Offset < 64` | 114,966 | 18 | `SetupNums`。添字がわからない書き込み |
| `x & 15 ≠ 0` | 210,820 | 0 | フレームの終わりで `timer` が決まらない |

参照の機械を書き換えた場合です。ロックをオフ: 1,204,601 ステップ、失敗 4552 で、フレームの終わりも受け入れられません。ページを 1: 211,021 ステップ、失敗 0 ですが、入るフレームの終わりのタイマーが `long` にならないので受け入れられません。ですから確認は中身のない形で通っているのではありません。

## 本物のフレームで確かめたこと

プログラムです（`screen-check`）。書き換えていない走りでは `SiteOK` の 7 つの部分のどれも失敗しません。土管の右に書き換えた走りでは、頭の読みが土管のタイルを読むので、頭の条件を満たさない命令があります。そのフレームには定理は使えません。それでもページとロックは変わりません。`Room` は最初の状態ですべて成り立ちます。「別の履歴」は、土管の上で乱数の入力のあと下を押した走りと、1-1 の開始で残機、コイン、スコア、ゲームタイマー、乱数を書き換えた走りです。

| 走り | フレーム | ポーズのフレーム | 入ったフレーム | 短いタイマー | `Room` の最初の状態 | `SiteOK` のフレームで `Room` も `Leaves` も出ない | `SiteOK` を満たさない命令 |
|---|---|---|---|---|---|---|---|
| TAS の部屋 | 111 | 0 | 1 | 0 | 1 / 1 | 0 | 0 |
| 本物の入る状態 13 個、別の履歴の 17 個、TAS から乱数の入力、右へ走る入力 | 130,030 | 28,315 | 20 | 0 | 31 / 31 | 0 | 0 |
| 同じ。最初の状態で大きいマリオに書き換え | 15,975 | 3,757 | 5 | 0 | 4 / 4 | 0 | 0 |
| 最初の状態でゲームタイマーを 100 の近くに書き換え、入力なし | 900 | 0 | 0 | 0 | 3 / 3 | 0 | 0 |
| 土管の右に書き換え、右と B、ポーズ | 4,800 | 2,328 | 0 | 0 | 12 / 12 | 0 | 192 |

* 入ったフレームのタイマーはどれも `long` です。
* どのフレームも `Room` か `Leaves` で終わります。
* 最も遅いハンドラの最後の命令はドット 43,009 で、`L` は 83,342 です。
* 右へ走って画面の外へ出ることはありません。スクロールロックがオンの間、`ChkPOffscr` が画面の中に戻します。土管の右に書き換えて右と B を押し続けても、位置は最大で 240 ピクセル、マリオのページは 0 のままです。

## 前提（Lean では証明していない）

* **`Room(seq(c))`.** 部屋で最初に操作できる状態の 73 バイト。ルートでは 5 バイトを除いて証明しました（[部屋で最初に操作できる状態の条件](d-2-4-1-ScreenStart-ja.md)）。以下はこのページを書いたときの説明です。走りが違っても変わらないバイトだけを `K` に残しました。ファイアマリオ（`PlayerStatus` が 2）では成り立ちません。1-1 のこの土管より前のパワーアップは 1 つです。部屋に入る切り替えの段を歩けば出るはずです。切り替えのあとの状態はほとんど知られているからです。項目 1-1-b-3-2 の段の最後の状態が `K` の値を知っていれば、`AS.le` の確認 1 つで済みます。`K` のうち面の準備が消さないバイトは `AreaType`、`CurrentPlayer`、`PlayerStatus`、`WorldNumber`、`OperMode`、`OperMode_Task`、`AreaMusicBuffer_Alt` です。その段の出口の条件がこれらを知る必要があります。ここではその段に頼っていません。動かしてもいません。
* **`SiteOK` の時間.** 部屋のフレームがはみ出さないことです。
* **読みの番地.** `LDA (zp),Y` がレジスタを読まないこと。
* **タイル.** ブロックバッファの読みが `T` の値を返すこと。読む番地がブロックバッファの中にあり、部屋のブロックバッファが初めの値かコインの消えた値であることから来ます。これは証明していません。
* **頭.** 頭の読みが 0 かコインであること。部屋では頭がレンガに届かないことから来ます。本物のフレームでは、ジャンプの高さが足りません（測定: 大きいマリオの `y` の最小は 45、頭の高さは最上段の下です）。
* **コインを消す番地、バッファの添字.** どちらも本物のフレームで成り立ちます。添字は 55 以下でした。
* **`x & 15 ≠ 0`.** [横の土管から地上への切り替え](d-1-SideTransition-ja.md) の `z` に届かないことです。この条件がないと切り替えは 378 フレームで、長くなる側ですが、`Entry2` は `timer ≥ 160` を求めます。
* **入るまでプレイヤーのルーチンで始まること.** 時間切れでこのルーチンから出ることはあります（確認には、けが、死、1 機減るルーチンで終わる道があります）。その走りは 1748 フレームよりずっと多く使っています。
* フレームはエミュレータのフレームです。

## [ルート](0-1-Route-ja.md) での使い方

`chg.entry₂` のタイマーの部分を次のもので置き換えられます（`entry_long`、非公開の `screen_entry`）。`Route.Changes` はこの形で、`Changes.run₂` が `entry_long` を使います。ROM の確認は `Route.RoomChecks` です。

```
entry₂     : Entry2 nm₂ nx₂ E 0 (seq a₂)            （タイマーの条件なし）
roomOrder  : b₁ ≤ a₂
roomRest   : RestAt(seq b₁)                            （5 バイト。Room(seq b₁) は Changes.roomAt）
roomSites  : ∀ n ∈ [b₁, a₂),  ∀ j,  SiteOK(tr_n(j))
roomStay   : ∀ n ∈ [b₁, a₂),  rt(seq n) = rt(r)
```

**リスト `K`**（名前）:

`GameEngineSubroutine`、`Enemy_Flag` (6)、`Enemy_ID+5`、`Player_State`（ビット 0xfc）、`Block_State` (2)、`Misc_State` (9)、`EnemyData`、`EnemyDataHigh`、`AreaMusicBuffer`（ビット 0xfb）、`AreaMusicQueue`、`FloateyNum_Timer` (6)、`VineFlagOffset`、`Block_RepFlag` (2)、`Cannon_PageLoc` (6)、`Cannon_X_Position` (6)、`Cannon_Y_Position` (4)、`EnemyFrenzyBuffer`、`SecondaryHardMode`、`EnemyFrenzyQueue`、`SprDataOffset`、`SwimmingFlag`、`JumpspringAnimCtrl`、`FireballThrowingTimer`、`ScreenLeft_PageLoc`、`ScreenRight_PageLoc`、`ScreenRight_X_Pos`、`AreaParserTaskNum`、`ScrollLock`、`EnemyDataOffset`、`EnemyObjectPageLoc`、`ScrollThirtyTwo`、`CloudTypeOverride`、`AreaType`、`CurrentPlayer`、`PlayerStatus`（ビット 0xfe）、`WorldNumber`、`OperMode`、`OperMode_Task`、`StarInvincibleTimer`、`AreaMusicBuffer_Alt`（ビット 0xfb）

**ファイル.** `Theorems/ScreenPage.lean`、非公開の `Proof/ScreenPage.lean`。

**再現.**
```
.lake/build/bin/smbrta screen-check FM2    # 確認、本物のフレームでの条件、約 104 秒
```
