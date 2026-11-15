[← Back](README-ja.md) | [English](f-6-19-FrameKeep.md) | [Japanese](f-6-19-FrameKeep-ja.md)

# 操作中の 1 フレーム全体は城の旗と端数の下のビットを保つ

**主張.** 操作中に始まる 1 フレーム全体は 2 つのことを保ちます。城の旗は立ちません。位置の端数は 1/16 ピクセルの倍数のままです。またフレームは、歩きに見える範囲で、操作中の次のフレームの始まりで終わります。待ちのループにいて、スタックポインタ、ドット、PPU がフレームの始まりのものです。フレームのどの命令もルーチン、モード、タスクのバイトを番地で書かないなら、フレームは操作中に終わります。これはどの機械、どの入力についても成り立つ定理です。条件はフレームの始まりの 1 つの状態と、フレームの各命令の 1 つの条件です。証明は [`PipeWrites`](a-5-2-PipeWrites-ja.md) と同じように、`TaintRun.lean` の抽象機械でフレーム全体を追います。

ですから `PoleJoin.Run` の仮定 `fracStep` はなくなりました。定理 `Run.fracP` です。走りのフレーム（フィールド `keep`）と ROM のチェックから出ます。フィールド `noCastle` もなくなりました。操作できるときの機械から出る定理 `Run.noCastle_of` です（[地上で操作できるときの機械](f-6-2-ControlStart-ja.md)）。フィールド `keep.start`（各フレームは操作中に始まる）もなくなりました。定理 `Frames.start` です。それにはもっと小さいフィールド `keep.ctl` が要ります。触る前の各フレームは操作中に終わる、というものです。

前の回、フィールド `keep.ends`、`keep.lag`、`keep.lagStart` がなくなりました。`keep` は、操作できるときからの全部のフレームを、数えるものも数えないものも、本物のフレームの列として持ちます（`all`、`inp`、`next`）。数えるフレームがどこで終わるかも持ちます（`ix`）。`lag` のフレームに専用の規則は要りません。歩きは、操作中に始まるどのフレームも覆います。ポーズ中かどうかは関係ありません。ですから `lag` のフレームも、数えるフレームと同じ定理（`Frames.all_start`）で、城の旗、端数の下のビット、操作中のフレームの始まりを保ちます。条件も同じ 2 つです。`ctl` と `clean` は、`lag` のフレームにもそれを聞くようになりました。

前の回、`ctl` は各フレームの終わりの 2 つのバイトを聞いていました。操作のルーチンとゲームのコアのタスクです。この回、フィールド `ctl` はなくなりました。3 つのバイトは `Prot_K` にあるので、`CleanK` のもとでは、添え字かポインタを通す書き込みはこれらを変えません。変えられるのは、どれかを番地で書く命令だけです。2 つ目の歩き（`ctlKeepCheck`、いまは `keepCheckOf` の一部）は、そういう命令で道を切ります。ほかの道はどれも、3 つのバイトが操作の値とわかったまま終わります。ですから新しいフィールド `keep.noStore` は、触るフレームの前のフレームのどの命令も 3 つのバイトのどれも番地で書かない、というものです。そういうフレームが操作中に終わることは定理です（`Frames.ctlAll`）。歩きはそういう命令に 8 つ来ます（下）。ですから `noStore` は、フレームが操作から出る 8 つの道を名指しします。触ること自体、土管、ダメージかパワーアップ、死ぬこと、ほかです。

この回、`keep` は数えるフレームを定義で決めます。フレームは、ゲームがポーズでない状態（ポーズのバイトの最下位ビットが 0）で終わるとき数えます。数えるフレーム `j` は `all(ix j)` で終わります。そういう終わりの `j` 番目です。なのでフィールド `ix` とその条件はなくなりました。[地上のフレーム](e-2-SurfaceFrames-ja.md) のフィールド `unpaused` と `lagPaused` もなくなりました。定義から成り立ちます（`Frames.up`、`Frames.down`）。新しいフィールド `many` は、あるフレーム `top` の終わりまでに `g` 個のフレームがポーズでない状態で終わる、というものです。また `clean` は、4 バイト多く守るガード（`guardF`）の `CleanK` を聞くようになりました。ポーズのバイト、エリアの種類、泳ぎのフラグ、大きさの変化です。なので地上のフレームのフィールド `spare` は `clean` の一部です。歩きはいまも `guardK` を使います。いまのフィールドは `cleanE` です。5 バイト多く守る `guardE` の `CleanK` です（`spareE`: A と B、前のフレームの A と B、動く向き、走りの速さ、覚えている速さ）。なので地上のフレームのフィールド `spareE` もその一部です（[触るまでのフレームの各命令](f-6-21-GuardE-ja.md)）。`Frames.cleanF` はいまは定理です。

いま `keep` は `seq` も持ちません（項目 1-1-f-6-22）。`Keep sy m0 S a g` です。`Frames` のフィールドから、機械 `seq` とフィールド `seqAt` を除いたものです。数えるフレーム `j` の終わりの機械は定義 `Keep.seq j = S.seq(a + ix j)` です。触る前もあとも、どの `j` でもそうです。`Keep.toFrames` は `seq := Keep.seq` とした前の `Frames` で、その `seqAt` は定義から成り立ちます。ですから `seqAt` はもう仮定ではありません。触ったあと城に入るまでのフレームも走りの本物のフレームです（[操作から城まで](f-5-PoleJoin-ja.md)、フィールド `toCastle`）。[地上のフレーム](e-2-SurfaceFrames-ja.md) はいまも `Frames` を `keep.toFrames` としてとります。

`frame(m, i)` は入力 `i` の本物の 1 フレームです。`tr(n)` はその中で `n` 命令あとの機械です。`all n` は、数えるかどうかによらず、フレーム `n` が始まるときの機械です。`all 0` は地上で操作できるときの機械です。`seq j` は数えるフレーム `j` の終わりの機械で、`seq 0 = all 0` です。

```
castle(m)        :=  StarFlagTaskControl(m) ≠ 0
f(m)             :=  SprObject_X_MoveForce(m)                         位置の端数（1/256 ピクセル単位）
Watched(m)       :=  castle(m) = false  ∧  f(m) mod 16 = 0
q                :=  MoveObjectHorizontally の最初の STA abs,X        端数を書く命令
Prot_K           :=  PipeWrites の Prot  ∪  {StarFlagTaskControl, SprObject_X_MoveForce}
Known_K(m)       :=  GameEngineSubroutine(m) = 操作  ∧  OperMode(m) = ゲーム  ∧  OperMode_Task(m) = コア
                  =  controllable(m)                                                     （known_of_ctl）
FrameStart_K(m)  :=  PipeWrites の FrameStart（待ちのループ、スタック、ドット、PPU、ストローブ）  ∧  Known_K(m)          （StartK）
CleanK(m)        :=  store:  添え字かポインタを通して書く命令、書く先 t:   ¬(pc(m) = q ∧ X(m) = 0)  →  Plain(Prot_K, t)
                     read, jump, time:  PipeWrites の `Clean` と同じ
Prot_F           :=  Prot_K  ∪  {pause, AreaType, SwimmingFlag, PlayerChangeSizeFlag}        （spareK。pause は CtrlKeep のポーズのバイト）
CleanK_F(m)      :=  Prot_K の代わりに Prot_F の CleanK(m)                                   （guardF の CleanK）
cleanK_of_F      :  CleanK_F(m)  →  CleanK(m)
Prot_E           :=  Prot_F  ∪  {A_B_Buttons, PreviousA_B_Buttons, Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute}   （spareE。ほかに collE、speedE、vertE、faceE、stateE: 1-1-f-6-21）
CleanK_E(m)      :=  Prot_K の代わりに Prot_E の CleanK(m)                                   （guardE の CleanK）
cleanK_of_E      :  CleanK_E(m)  →  CleanK_F(m)
```

`Plain(Prot_K, t)` は、その書き込みが `Prot_K` のバイトを変えないことです。`q` で `X = 0` の書き込みはプレイヤー自身の端数の書き込みなので、聞きません。

```
keep_frame        :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n)))   →   Watched(frame(m, i))
keep_frame_start  :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  Known_K(frame(m, i))
                       →   FrameStart_K(frame(m, i))  ∧  Watched(frame(m, i))

RealRun S         :  S.seq n, S.inp n,  S.seq(n + 1) = frame(S.seq n, S.inp n)      走り全体の本物のフレーム
up(n)             :=  pause(all n) & 1 = 0                                  all n で終わるフレームはポーズでない状態で終わる
upTo(n)           :=  #{ k ∈ [1, n] : up(k) }
ix j              :=  min { n ≤ top : j ≤ upTo(n) }                         ポーズでない状態で終わる j 番目のフレーム（定義、ixOf）
Frames (keep)     :  all n := S.seq(a + n),  inp n := S.inp(a + n)        フレーム n が始まる機械（数えるかどうかによらない）と、その入力（定義）
                     next    :  all(n + 1) = frame(all n, inp n)              （定理 Frames.next）
                     seq0    :  seq 0 = S.seq a                                （定理 Frames.seq0）
                     top, many :  g ≤ upTo(top)                                 フレーム top の終わりまでに g 個のフレームがポーズでない状態で終わる
                     seqAt   :  j ≤ g → seq j = all(ix j)                       数えるフレーム j は seq j で終わる
                     noStore :  n + 1 < ix g  →  ∀ k,  ¬CtlStore(tr_n(k))
                     cleanE  :  n < ix g  →  ∀ k,  CleanK_E(tr_n(k))               tr_n:  all n からのフレームの命令
Keep (keep)       :  top, many, noStore, cleanE は Frames と同じ。seq と seqAt はない
Keep.seq j        :=  S.seq(a + ix j)                                       どの j でも（定義）
Keep.toFrames     :  seq := Keep.seq とした Frames。seqAt は定義から
Keep.up_at        :  1 ≤ j ≤ upTo(top)  →  pause(seq j) & 1 = 0             触る前もあとも
Keep.ends_at      :  1 ≤ j ≤ upTo(top)  →  seq j = frame(all(ix j − 1), inp(ix j − 1))
Frames.ix0        :  ix 0 = 0
Frames.order      :  j < g  →  ix j < ix(j + 1)
Frames.up         :  1 ≤ j ≤ g  →  pause(seq j) & 1 = 0                      OnFrames の前のフィールド unpaused
Frames.down       :  1 ≤ j ≤ g,  ix(j − 1) ≤ n,  n + 1 < ix j  →  pause(all(n + 1)) & 1 = 1      OnFrames の前のフィールド lagPaused
Frames.cleanF     :  n < ix g  →  ∀ k,  CleanK_F(tr_n(k))                    前のフィールド cleanF
Frames.clean      :  n < ix g  →  ∀ k,  CleanK(tr_n(k))
fm j  :=  all(ix j − 1),   pad j  :=  inp(ix j − 1)                       数えるフレーム j が始まる機械と、その入力
AtCtl(m)          :=  FrameStart_K(m)  ∧  castle(m) = false                 操作できるときの機械
Frames.ends       :  keep  →  ∀ j,  1 ≤ j ≤ g  →  seq j = frame(fm j, pad j)
Frames.all_start  :  keepCheck,  keep,  FrameStart_K(seq 0),  Watched(seq 0)   →   ∀ n < ix g,  FrameStart_K(all n)  ∧  Watched(all n)
Frames.all_watched:  同じもの   →   ∀ n ≤ ix g,  Watched(all n)
Frames.run        :  同じもの   →   ∀ j < g,  FrameStart_K(seq j)  ∧  Watched(seq j)
Frames.start      :  同じもの   →   ∀ j,  1 ≤ j ≤ g  →  FrameStart_K(fm j)
Frames.watched    :  同じもの   →   ∀ j ≤ g,  Watched(seq j)
Frames.ctlAll     :  同じ仮定   →   ∀ n,  n + 1 < ix g  →  controllable(all(n + 1))

CtlStore(m)       :=  pc(m) の命令は STA、STX、STY、INC、DEC、ASL、LSR、ROL、ROR のどれか（ゼロページか絶対番地）で、
                      その番地（0x2000 より下、2048 で割った余り）は GameEngineSubroutine、OperMode、OperMode_Task のどれか
keep_frame_startC :  ctlKeepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  (∀ n,  ¬CtlStore(tr(n)))
                       →   FrameStart_K(frame(m, i))  ∧  Watched(frame(m, i))

endCtl(B)         :  rt(B) は操作でないとわかる  ∨  タスクはコアでないとわかる  ∨  モードはゲームとわかる
ctl_of_frame      :  keepCheckOf,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  rt(frame(m, i)) = 操作,  タスク(frame(m, i)) = コア
                       →   controllable(frame(m, i))

Run.watched₀      :  Start(seq 0),  fracCheck,  castle(seq 0) = false   →   Watched(seq 0)
Run.fracP         :  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0),  Run   →   ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac          :  同じもの  →  P₂(g) mod 16 = 0
Run.noCastle_of   :  同じもの  →  ∀ j ≤ g,  castle(seq j) = false
```

`P(j)` は機械から読んだ `posP(seq(j − 1))` です（`frames.reads`）。`AtCtl(seq 0)` は本物の走りの上の定理 `ControlStart.EndRun.atCtl` です。横の土管から出る切り替えの段から出ます（[地上で操作できるときの機械](f-6-2-ControlStart-ja.md)）。

`Frames.all_start` は `n` についての帰納法です。数えるかどうかによらず、全部のフレームをたどります。フレーム `n` は `all n` で `FrameStart_K` と `Watched` で始まります。`all(n + 1)` で終わります（`next`）。`keep_frame_startC` が、フレーム `n` の `noStore` から、`FrameStart_K(all(n + 1))` と `Watched(all(n + 1))` を出します。触るフレームは最後のフレーム（`n = ix g − 1`）で、操作中に終わることを聞きません。そこでルーチンが変わるからです。`keep_frame` はそれなしで `Watched(all(ix g))` を出します（`Frames.all_watched`）。数えるフレームについての定理は、これを `seq j = all(ix j)` と `fm j = all(ix j − 1)` で読みます。`ix` は増えるので `ix j ≤ ix g` です（`Frames.ix_mono`）。

## 抽象機械の歩き

`PipeWrites` の歩きと同じです。書く先がわからない書き込みは `Prot_K` の外のバイトを全部忘れます。ジャンプのルーチンでは添え字を表の項目に分けます。時間には上限をつけます。始まりは `PipeWrites` の状態に、城のバイトが 0 で端数の下 4 ビットが 0 とわかっていることを足したものです。どの道もフレームの終わりで、`Watched` がわかっていることと、フレームの始まりの状態であること（`endOK`）を確かめて終わります:

```
endOK(B)  :=  pc(B) = 待ちのループ  ∧  S(B) = S₀  ∧  ((lo = hi = 0  ∧  ¬vblank  ∧  ¬nmi)  ∨  (1 ≤ lo  ∧  hi ≤ 9  ∧  vblank  ∧  nmi))
              ∧  ppuCtrl(B) のビット 7 が 1 とわかる  ∧  ¬strobe(B)
```

`start_of_sim` は、`endOK(B)` と、`B` が覆う機械と、その機械の `Known_K` から `FrameStart_K` を出します。歩きはフレームの終わりで `Known_K` を知りません。表のキーにはルーチンのバイトがありますが、モードとタスクはありません。ですから表はモードとタスクについて状態をまとめてしまいます。表の 46,573 の状態のうち 45,808 は、モードとタスクを知りません。`GameCoreRoutine` が `GameRoutines`（ルーチンのバイトのルーチン）から戻るところと、`PlayerSubs` が当たり判定のルーチンから戻るところで、まとめるときに失われます。これは `keepCheck` の歩きです。パート a の `StartRun` もこれを使います。

**走りのフレームの歩き（`keepCheckOf`）.** 表のキーにモードとタスクを入れます（証明の一部ではありません）。そしてフレームのどの終わりでも、`Watched` と `endOK` のほかに `endCtl` を聞きます。表は 46,576 の状態です。前の回、同じキーの試しの歩き（同じ表）は、フレームのどの終わりでも 3 つのバイトを知っていました。終わりは 34 個で、3 つのバイトの組は 17 種類です。そのうち 4 個は、ルーチンが操作のもので、タスクが 0 です。2 個はモードがゲーム、2 個はモードが 2 です。歩きはこれらを `ChgAreaMode`（面の切り替え: タスク 0）と `HandleAxeMetatile`（斧: タスク 0 とモード 2）で書きます。どちらもルーチンのバイトは書きません。ですから、フレームの終わりでルーチンが操作のものでも、操作中とは言えません。`ctl` は 1 バイトにはできません。ルーチンが操作のもので、タスクがゲームのコアのものである終わりでは、どれもモードはゲームのものです（`endCtl`）。ですから `ctl` はルーチンとタスクだけを聞き、モードは `ctl_of_frame` から出ます。

この歩きだけのステップが 2 つあります。

* **下のビットの足し算.** `A` の下 4 ビット、バイトの下 4 ビット、キャリーがわかっている `ADC zp` は、和の下 4 ビットがわかります: `(a + b + c) mod 16 = (a mod 16 + b mod 16 + c) mod 16`（`s_adcL`、`adc` に対して証明）。移動のルーチンはこうして `16·v` を足します。速さを 4 回左にずらしたものは下 4 ビットが 0 です。
* **移動のルーチンの添え字.** その入り口で、わからない添え字 `X` を 9 つに分けます: `X = 0`、または `X` の一番下の 1 のビットがビット `b`（`b = 0, …, 7`）。`X = 0` なら書く先がわかります。`X ≠ 0` なら `PipeWrites` のいつもの書き込みで、`CleanK` がその書く先は `Plain` だと言います。プレイヤーの移動は `X` をジャンプ台の制御からとります。9 つに分けるので、そのバイトに条件は要りません。

**触る前のフレームの歩き（`ctlKeepCheck`）.** 同じ歩きに、規則を 1 つ足したものです。ルーチン、モード、タスクを番地で書く命令で道を止めます（`walkKC`）。仮定 `noStore` から、フレームはそこに来ません。フレームのどの終わりでも、`Watched`、`endOK`、3 つのバイトが操作の値とわかっていること（`knownAll`）を聞きます。すると `endOK` と 3 つのバイトから次のフレームの `FrameStart_K` が出ます（`start_of_sim`）。値から `controllable` が出ます（`ctl_of_known`）。ROM には 3 つのバイトのどれかを番地で書く命令が 37 個あります。歩きはそのうち 8 個に来ます:

| コードの場所 | 書くもの |
|---|---|
| `PlayerHole` | 命を失うルーチン: 穴に落ちる |
| `ChgAreaMode` | タスク 0: 面の切り替え |
| `SetPRout` | ダメージ、敵か時間による死、パワーアップのルーチン |
| 横の土管に入るところ（`ChkGERtn` のあと） | 横の土管のルーチン |
| `HandleAxeMetatile` | タスク 0（そのあとモード）: 斧 |
| `RunFR`（旗） | 旗のルーチン: 触ること |
| `VineCollision` | 画面の上でのぼるルーチン |
| 縦の土管に入るところ | 縦の土管のルーチン |

チェック `keepCheckOf`（非公開の証明では `keep_check`）は表の最初の 2 行です。両方の歩きです。フレームの終わりは、1 つ目ではどれも `endOK` と `endCtl` を満たし、2 つ目ではどれも `endOK` と操作の 3 つのバイトを満たします。

| 歩き | ステップ | 分かれ | 失敗 | 表 | 時間 |
|---|---|---|---|---|---|
| 城の旗と端数、9 つに分ける、キーにモードとタスク、終わりで `endOK` と `endCtl`（`keepCheckOf` の 1 つ目） | 707,869 | 69,388 | 0 | 46,576 | プログラムで探すのに 2.8 秒、チェック 3.9 秒 |
| 同じもので、3 つのバイトの書き込みで道を切り、終わりで `endOK` と操作の 3 つのバイト（`ctlKeepCheck`、この回） | 67,115 | 6,987 | 0 | 4,520 | プログラムで探すのに 0.1 秒、チェック 0.2 秒 |
| 城の旗と端数、9 つに分ける、終わりで `endOK`（`keepCheck`、前の回） | 707,685 | 69,404 | 0 | 46,573 | プログラムでチェック 3.8 秒、`Proof.FrameKeep` 5.0 秒 |
| 同じもので、ジャンプ台の制御が始まりで 0 とわかり `Prot_K` にある（前の回） | 1,044,377 | 101,574 | 0 | 79,266 | プログラムでチェック 4.9 秒 |
| 城の旗だけ、分けない | 907,094 | 92,482 | 0 | 72,016 | チェック 4.5 秒 |
| 城の旗と端数、`X` を 256 の値に分ける | 9,779,840 | 767,686 | 0 | 355,602 | チェック 32 秒 |

## 本物のフレームで

最後の変更のあとの `keep-frames-check FM2 100` です。`cleanE` のガード `guardE` を使います（終了コード 0、悪いもの 0）。地上で操作できるときから触るまでの全部のフレーム（触るフレームも入れて、数えるかどうかによらず）です。はじめの 4 種類の走りは Start がないので `lag` のフレームはありません。5 番目は 1 つのフレームで Start を押し、10〜49 フレームあとにもう一度押します。これは旗まで行きません。最後のものはムービーのフレーム 1002〜1091 から始め、1 つのフレームで Start を押し、ポーズのタイマーのあと、44〜73 フレームあとにもう一度押します。ゲームは続きます。この走りのうち 241 が旗に触り、触る前にポーズ中のフレームが 12,671 あります。

| 走り | 走りの数 | フレーム | 命令 | 触り |
|---|---|---|---|---|
| ムービーの、操作から触るまで | 1 | 240 | 1,203,506 | 1 |
| 操作からランダムな入力 | 100 | 29,102 | 150,058,083 | 0 |
| ムービーのフレーム 1002〜1091 からランダムな入力 | 400 | 46,025 | 183,000,496 | 216 |
| 画面の左端へ入ってからランダム | 120 | 35,945 | 193,591,853 | 0 |
| 操作からポーズのあるランダムな入力 | 100 | 37,395（ポーズ中 26,341） | 107,816,920 | 0 |
| ムービーのフレーム 1002〜1091 からポーズのあるランダムな入力 | 400 | 76,106（ポーズ中 24,517） | 250,174,812 | 241 |

* どのフレームも `FrameStart_K` を満たし、`Watched` で始まります。どの命令も `CleanK` を満たします。どのフレームも `Watched` で終わります。
* 操作のルーチンで終わるフレームはどれも、`controllable` で終わります。旗に触る走りでは、触るフレームの前のどのフレームも、ポーズ中のものも、操作のルーチンで終わります。
* 旗に触る走りでは、触るフレームの前のどのフレームにも、ルーチン、モード、タスクを番地で書く命令はありません。ですからこれらの走りで `noStore` が成り立ちます。そういう命令のあるフレームは、ムービーで 1、ムービーのフレームからの走りで 216 と 241 で、どれも触るフレームです（`RunFR`、直接つかむときはそのあと面の終わり）。操作からのランダムな走り、左端への走り、操作からのポーズのある走りでは 44、7、15 で、どれも `SetPRout` で、触らない走りです。
* 条件を満たし、そういう命令のないフレームはどれも、`controllable` で終わります（`keep_frame_startC` と `ctl_of_known` のとおり）。
* `q` で `X = 0` の書き込みは、ポーズ中でないどのフレームにも 1 回あります。プレイヤーの移動です。添え字かポインタを通すほかの書き込みは `Prot_E` に触れません（なので `Prot_F` にも `Prot_K` にも触れません）。
* 命令の一番遅いドットは 66,674 で、上限 `dotsPerFrame − 64` より下です。

**数えるフレーム.** `count-frames-check FM2 100`（終了コード 0、悪いもの 0、約 40 秒）は、操作できるときから触るまでのフレーム（触るフレームも入れて）を走らせ、フレームを数える 2 つのやり方を比べます。ポーズでない状態で終わる（`up`、`keep` の定義）か、位相が動く（`CastleToLevel.kindOf` が `lag` でない、時計の数え方）かです。Start はランダムに押します（41 フレームに約 1 回）。ムービーの触る前のフレームの 1 つでも押し、45 フレームあとにもう一度押します。

| 走り | 走りの数 | フレーム | ポーズで終わる | 2 つのやり方が違う | 触り | ポーズで終わる触り | `spareK` への添字での書き込み |
|---|---|---|---|---|---|---|---|
| ムービーの、操作から触るまで | 1 | 240 | 0 | 0 | 1 | 0 | 0 |
| 操作からランダムな入力（3 分の 1 は Start あり） | 100 | 30,830 | 6,905 | 0 | 0 | 0 | 0 |
| ムービーのフレーム 1002〜1091 からランダムな入力（半分は Start あり） | 400 | 52,237 | 15,990 | 0 | 170 | 0 | 0 |
| ムービーの触る前の 11 フレームの 1 つで Start | 77 | 6,542 | 2,970 | 0 | 32 | 0 | 0 |

なのでこれらの走りでは、`keep` の数えるフレームは時計が数えるフレームです。また `top` を触るフレームにとれば `many` が成り立ちます。触るフレームはポーズでない状態で終わります。

**地上のフレームが来る、3 つのバイトの書き込み（`noStore`）.** `keep-reach-search` は `ctlKeepCheck` の探索を、操作中のフレームの始まりから走らせます。触るフレームより前のどのフレームについても証明したことを使います: 城の旗が立っていない、端数の下のビットが 0、操作のときのエリアの種類、泳ぎのフラグ 0、大きさの変化 0（`OnFrames.areaAll`）。ガードは `guardF` です。それでも上の表の 8 か所すべてに来ます（125,034 ステップ、表は 7,574 の状態、0.4 秒）。なのでいままでに証明したことは、どの場所も除きません。コードによると、それぞれに要るものは次のとおりです。

| 場所 | 要るもの | 証明したか |
|---|---|---|
| `PlayerHole` | 画面の下にいる（穴） | いいえ: フレーム 8 よりあとの高さは仮定（1-1-f-6-4、1-1-f-6-5） |
| `ChgAreaMode` | 操作中のフレームからは、コードでは雲の面の `PlayerHole` を通るときだけ | いいえ、`PlayerHole` と同じ |
| `SetPRout` | 敵かパワーアップが触る、または時間が切れる | いいえ: 旗の近くに敵がいないことは仮定（1-1-f-6-14）。本物の走りでも操作から 44 回来ます。どれも触らない走りです |
| 横の土管に入るところ | 横に横の土管のタイル | いいえ: 地図は仮定（1-1-f-6-6） |
| `HandleAxeMetatile` | 足もとに斧のタイル | いいえ: 地図 |
| `RunFR` | 横に旗のタイル: 触ること | 触るフレームです。その前のフレームがここに来れば触りなので、`g` が最初の触りだということです |
| `VineCollision` | 画面の上のほうでつるのタイル | いいえ: 地図 |
| 縦の土管に入るところ | 下を押していて、足もとにワープ土管の上 | いいえ: 地図 |

上の本物の走りでは、触るフレームより前のフレームはどこにも来ません。触るフレームは `RunFR` に来ます。

**操作できるときの敵（1-1-f-6-14）.** 地上で操作できるときの敵のスロットの条件で、歩きが保つものでは、`SetPRout` を除けません。ムービーでは、操作できるときにもう 2 体の敵が読み込まれています。フレーム 852 で 2 つのスロットのフラグが 1 で、種類はクリボーです（ディスアセンブリの `Enemy_Flag` と `Enemy_ID` を `tas-peek FM2 852 1092` で見ます）。それぞれフレーム 951 と 1011 までにスロットから消えます。エリアの読み込みは、フレーム 1011 までに旗をスロットに入れ、フレーム 1051 までに城の旗を入れます。ですからスロットは操作できるときに空ではなく、フレームは地図からスロットを埋めます。歩きは地図を知りません。敵が触るかどうかはマリオの道筋で決まり、1 つの状態では決まりません。上の操作からのランダムな走りで `SetPRout` に来る 44 フレームは、どれも触らない走りです。

## 仮定（Lean で証明していないもの）

* **`keep.cleanE`: 触るまでの各フレーム（数えるかどうかによらず）の各命令の `CleanK_E`.** `PipeWrites` の条件に、3 つのバイト、`spareK` の 4 バイト、`spareE` の 5 バイトを守るバイトに足し、プレイヤーの書き込みを聞かないことにしたものです。[地上のフレーム](e-2-SurfaceFrames-ja.md) の前のフィールド `spare` と `spareE` を含み、触るフレームにもそれを聞きます。上の本物のフレームで確かめました。
* **`keep.noStore`: 触るフレームの前のフレーム（数えるかどうかによらず）のどの命令も、ルーチン、モード、タスクを番地で書かない.** 各命令の条件です。歩きはそういう場所に 8 つ来ます（上）。どれも操作から出る道です。フレームが操作中に終わることは定理です（`Frames.ctlAll`）。`noStore` と歩きから前の `ctl` が出るので、`noStore` は `ctl` より弱くはありません。終わりのバイトの代わりに、コードの場所を名指しします。
* **`keep.top`、`keep.many`: フレーム `top` の終わりまでに `g` 個のフレームがポーズでない状態で終わる.** 数えるフレーム `j` は `seq j = S.seq(a + ix j)` で終わります。これは定義です（フィールド `seqAt` はなくなりました）。走りがどの機械でできているかを言うものです。どのフレームを数えるかは定義です。ポーズでない状態で終わるフレームです。フレームそのものはもうフィールドではありません。`Frames` は走り全体の本物のフレーム（`RealRun`）と操作のフレーム `a` をとり、`all n = S.seq (a + n)`、`inp n = S.inp (a + n)` は定義です。`next` と `seq 0 = S.seq a` は定理です（`Frames.next`、`Frames.seq0`）。なので地上で操作できるときの機械は、走りの 2 つ目の切り替えの終わりの機械です（`Route.Run.atCtl`、項目 1-1-0-4）。

仮定でなくなったもの: `fracStep`（各フレームは位置を 1/16 ピクセルの倍数だけ動かす）、そのあと `noCastle` と `keep.start`、そのあと `keep.ends`（`Frames.ends`）、`keep.lag` と `keep.lagStart`（`Frames.all_start`）。`CleanK` と `FrameStart_K` はもうジャンプ台の制御を名指ししません。新しいもの: `keep`（`all`、`inp`、`next`、`ix`、`ctl`、`clean`）と ROM のチェック `keepCheck`、`ControlStart.ctlCheck`。そのあと、モードが `ctl` からなくなり、`keepCheckOf` は `endCtl` を聞く歩きになりました。そのあと、`all`、`inp`、`next` はフィールドでなくなりました（`RealRun` からの定義）。そのあと、`ctl` がフィールドでなくなり、`noStore` が入りました。`keepCheckOf` は 2 つ目の歩き `ctlKeepCheck` を持ちます。この回、`ix`（`ix0`、`order` も）がフィールドでなくなり、`top`、`many`、`seqAt` が入りました。地上のフレームのフィールド `unpaused`、`lagPaused`、`spare` はなくなりました。`clean` は `cleanF` になりました。そのあと、`seq` と `seqAt` がなくなりました（`Keep`。`seq` はどのフレームでも定義）。そのあと、`cleanF` は `cleanE` になり（5 バイト多く守る）、地上のフレームのフィールド `spareE` がなくなりました。

**変えたことで多く聞くもの.** `noStore`（前は `ctl`）と `clean` は、数えるフレームに聞くことを `lag` のフレームにも聞きます。操作中に終わらない `lag` のフレームは `noStore` の外です。コードによると、大きいマリオがダメージを受けたあとの、タイマーを止める制御のフレームがそうです。ダメージはダメージのルーチンとタイマーを止める制御を一緒に書きます。前の `lag` と `lagStart` は、城の旗、端数の下のビット、操作中のフレームの始まりが `lag` のフレームを通って保たれることだけを聞いていました。ですからそういう走りでも成り立ちえました。ポーズ中のフレームは操作中に終わります。

**ファイル.** `Theorems/FrameKeep.lean`、`Theorems/ControlStart.lean`、`Theorems/PoleJoin.lean`、非公開の `Proof/FrameKeep.lean`、`Proof/ControlStart.lean`。

**確かめ方.**
```
.lake/build/bin/smbrta keep-check                     # 歩きをプログラムで（約 10 秒）
.lake/build/bin/smbrta keep-ctl-search                # endCtl を聞く keepCheckOf の歩き（約 12 秒）
.lake/build/bin/smbrta keep-store-search              # 3 つのバイトの書き込みで切る歩き（ctlKeepCheck）と、keepCheckOf の両方の歩き（約 4 秒）
.lake/build/bin/smbrta keep-frames-check FM2 100      # 本物のフレームで条件を、guardE で（約 4 分）
.lake/build/bin/smbrta count-frames-check FM2 100     # 数えるフレーム、触るフレーム、spareK への書き込み（約 40 秒）
.lake/build/bin/smbrta keep-reach-search              # 始まりで証明したことを使って、歩きが来る noStore の場所（約 1 秒）
```
