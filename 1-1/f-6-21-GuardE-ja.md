[← Back](README-ja.md) | [English](f-6-21-GuardE.md) | [Japanese](f-6-21-GuardE-ja.md)

# 触るまでのフレームの各命令

**主張.** 走りは、地上で操作できるときから触るまでの各フレーム（数えるかどうかによらず）の各命令に、1 つの条件を仮定します。`keep.cleanE` です。ガード `guardE` の `CleanK` です。このもとでは、添字かポインタを通す書き込みは守るバイトを書きません。プレイヤー自身の端数の書き込みは聞きません。この回、`guardE` は `guardF` より 5 バイト多く守ります。A と B、前のフレームの A と B、動く向き、走りの速さ、覚えている速さです。ですから [地上のフレーム](e-2-SurfaceFrames-ja.md) のフィールド `spareE` はなくなりました。同じ 5 バイトを各命令に聞くものでした。

`spareE` を使っていた定理は 2 つです。前のフレームの A と B の歩き（`PrevKeep.prev_end`）と、スクロールの処理からフレームの終わりまでの横の 3 バイトの歩き（`AfterKeep.keepH`）です。どちらも `guardF` の `CleanK` と、各命令の `SpareAB` か `SpareH` を聞きます。両方を使うのは、歩きのガードの `CleanK` を出すためだけです。そのガードも、プレイヤー自身の端数の書き込みを聞きません。ですから `guardE` の `CleanK` からそれがじかに出ます。`GuardE.prev_endE` と `GuardE.keepHE` は、条件を `CleanK_E` 1 つにした同じ 2 つの定理です。歩きも、ROM のチェックも、証明も同じです。

`tr(n)` はフレームの中で `n` 命令あとの機械です。`Prot_K`、`Prot_F`、`CleanK`、`q` は [操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md) のものです。`t(m)` は `m` で添字かポインタを通す書き込みの行き先です。`idx(t) = t mod 2048` です。

```
spareE           :=  {A_B_Buttons, PreviousA_B_Buttons, Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute}
Prot_E           :=  edgeE  ∪  parE  ∪  stateE  ∪  faceE  ∪  spareE  ∪  collE  ∪  speedE  ∪  vertE  ∪  Prot_F    （guardE、29 回目の前は 70 バイト。29 回目に parE = エリアの解析の 4 つのバイト（残りのタスクの数、32 px のスクロールのカウンタ、列、ページ。1-1-f-6-17-10）。26 回目に edgeE = 画面の左端のピクセルとページ（1-1-e-2-10-3-13）。27 回目にスクロールへの足場の力を加えた（1-1-e-2-10-3-14）。15 回目に stateE = {Player_State, VerticalForce} と faceE = {PlayerFacingDir, Player_X_MoveForce} を加えた。13 回目に collE = {Player_CollisionBits}、14 回目に speedE = {Player_X_Speed} と vertE = {VerticalForceDown, JumpOrigin_Y_Position, DiffToHaltJump} を加えた。パート e の `spareC`、`spareV`、`vAfter` の 4 つのバイトは `keep.cleanE` から）
CleanK_E(m)      :=  Prot_K の代わりに Prot_E の CleanK(m)
keep.cleanE      :  n < ix g  →  ∀ k,  CleanK_E(tr_n(k))                               （フィールド。前は cleanF で Prot_F）

cleanK_of_E      :  CleanK_E(m)  →  CleanK_F(m)
Frames.cleanF    :  keep  →  n < ix g  →  ∀ k,  CleanK_F(tr_n(k))                       （いまは定理）
cleanK_sub       :  CleanK_G(m),  Prot_G' ⊆ Prot_G,  G' のほかの部分は G のもの   →   CleanK_G'(m)
cleanAB_of_E     :  CleanK_E(m)  →  PrevKeep.guardAB の CleanK(m)                         Prot = {A_B_Buttons, PreviousA_B_Buttons} ∪ Prot_F
cleanH_of_E      :  x ∈ hI,  CleanK_E(m)  →  AfterKeep.guardH x の CleanK(m)              Prot = {x} ∪ Prot_F,  hI = {Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute}

SpareE(m)        :=  ∀ t,  t(m) = t  →  t < 0x2000  →  idx(t) ∉ spareE                  （AfterKeep.SpareE: 前のフィールド spareE）
spareE_of        :  CleanK_E(m),  ¬(pc(m) = q ∧ X(m) = 0)   →   SpareE(m)

prev_endE        :  ctrlCheck,  prevCheck v,  FrameStart_K(m),  (∀ n, CleanK_E(tr(n))),  (∀ n, ¬CtlStore(tr(n))),  AreaOK_v(m),  PrevOK(m)
                       →   PrevOK(frame(m, i))
keepHE           :  ctrlCheck,  hCheck v,  FrameStart_K(m),  (∀ n, CleanK_E(tr(n))),  (∀ n, ¬CtlStore(tr(n))),  AreaOK_v(m),
                    pc(tr(n₀)) = PlayerCtrlRoutine（フレームの中で最初）
                       →   ∀ k ≥ n₀,  pc(tr(k)) = PlayerSubs  →  ∀ x ∈ hI,  x(frame(m, i)) = x(tr(k))
```

`PrevOK(m)` は、前のフレームの A と B の 7 ビット目が A と B の 7 ビット目と同じことです。`OnFrames.prevAll` と `OnFrames.movesAt` は、`keep.cleanF` と `spareE` で `prev_end` と `keepH` を使う代わりに、`keep.cleanE` で `prev_endE` と `keepHE` を使うようになりました。ほかの型は変わっていません。

## `CleanK_E` からどこでも `SpareE` が出るわけではない理由

`CleanK` は `q` で `X = 0` の書き込みを聞きません。プレイヤー自身の端数の書き込みで、歩きはその行き先を知っています。`SpareE` はどの命令にも聞きます。ですから `CleanK_E` から `SpareE` が出るのは、その命令以外です（`spareE_of`）。その命令の行き先は端数のバイトなので、本物のフレームでは `SpareE` が成り立ちます。証明には、ROM の `q` の命令と、機械のプログラムのバイトがフレームの中で変わらないことが要ります。2 つ目の補題はまだありません。要りもしません。`prev_end` と `keepH` の歩きは、その書き込みに何も聞かないからです。

## 新しいガードにした理由

`guardF` はパート e の歩きのガードでもあります。`PrevKeep.guardAB` は A と B も守る `guardF`、`AfterKeep.guardH x` は `x` も守る `guardF` で、`AfterKeep` の 1 つ目の歩きは `guardF` を使います。その表は、`CtrlKeep.spareI` のバイトを守る探索から作ります。5 バイトを `spareK` に足すと、これらの歩きと、そのチェック `prevCheck`、`hCheck` が変わります。ですから 5 バイトは各命令の条件（`guardE`）でだけ守り、歩きでは守りません。歩きも ROM のチェックも変わらず、非公開の証明も長くなっていません。

## 本物のフレームで

`keep-frames-check FM2 100` は、地上で操作できるときから触るまで（触るフレームも、数えるかどうかによらず）の本物のフレームのすべての命令で `CleanK` を確かめます。この回はガード `guardE` を使います（終了コード 0、悪いもの 0、4 分 39 秒）。プレイヤーの端数の書き込みのほかに、添字かポインタを通す書き込みは `Prot_E` に触れません。

| 走り | 走りの数 | フレーム | 命令 | 触り | `Plain` でない書き込み |
|---|---|---|---|---|---|
| ムービーの、操作から触るまで | 1 | 240 | 1,203,506 | 1 | 0 |
| 操作からランダムな入力 | 100 | 29,102 | 150,058,083 | 0 | 0 |
| ムービーのフレーム 1002〜1091 からランダムな入力 | 400 | 46,025 | 183,000,496 | 216 | 0 |
| 画面の左端へ入ってからランダム | 120 | 35,945 | 193,591,853 | 0 | 0 |
| 操作からポーズのあるランダムな入力 | 100 | 37,395 | 107,816,920 | 0 | 0 |
| ムービーのフレーム 1002〜1091 からポーズのあるランダムな入力 | 400 | 76,106 | 250,174,812 | 241 | 0 |

[地上のフレーム](e-2-SurfaceFrames-ja.md) の `after-real FM2 100` は、地上の操作中の本物のフレームのすべての命令で `SpareE` を確かめます。プレイヤーの書き込みも入れてです（終了コード 0、1 分 21 秒）。添字かポインタを通して `spareE` のバイトに書くフレームはありません。ムービーの操作からの 240 フレーム、操作からのランダムな走りの 19,870 フレーム、Select ありの 5,316 フレーム、Start ありの 10,376 フレームのどれにもです。

## 仮定（Lean で証明していないもの）

* **`keep.cleanE`: 触るまでの各フレーム（数えるかどうかによらず）の各命令の `CleanK_E`.** 1 つの機械の条件です。地上のフレームの前のフィールド `spare` と `spareE` を含み、触るフレームと `lag` のフレームにもそれを聞きます。

仮定でなくなったもの: `OnFrames` のフィールド `spareE`（`PoleJoin.Run.frames.spareE`）。変わったもの: フィールド `keep.cleanF`（`guardF` の `CleanK`）は `keep.cleanE`（`guardE` の `CleanK`、5 バイト多い）になりました。`Frames.cleanF` は定理です。

**ファイル.** `Theorems/GuardE.lean`（新しい）、`Theorems/FrameKeep.lean`（`spareE`、`guardE`、`cleanK_of_E`、`cleanK_sub`、フィールド `cleanE`）、`Theorems/SurfaceFrames.lean`（フィールド `spareE` を除いた。`prevAll`、`movesAt`）。

**確かめ方.**
```
.lake/build/bin/smbrta keep-frames-check FM2 100      # 地上の本物のフレームで guardE の CleanK（約 5 分）
.lake/build/bin/smbrta after-real FM2 100             # 本物のフレームで SpareE（パート e）
```
