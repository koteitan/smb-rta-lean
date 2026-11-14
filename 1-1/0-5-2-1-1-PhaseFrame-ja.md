[← Back](README-ja.md) | [English](0-5-2-1-1-PhaseFrame.md) | [Japanese](0-5-2-1-1-PhaseFrame-ja.md)

# 操作中の 1 フレームは、ポーズで終わるときにちょうど位相を保つ

**主張.** フレームが、操作中のアイドルループで始まり（`StartK`）、タイマーの親の制御が 0、位相が 20 以下で、すべての命令が `guardPh` の `CleanK` を満たすとします。するとそのフレームは、ポーズで終わって始めの位相のままか、ポーズでなく終わって位相が `(p + 20) % 21` になるかです。これは時計の位相の規則です。触るフレームより前のフレームは、タイマーの親の制御も 0 のまま保ちます。なので `pole.keep` の、触るフレームまでの各フレームはこの規則に従います。

位相は、間隔タイマーの制御（`IntervalTimerControl`）です。時計の `phase`（`CastleToLevel.Frames.ph`）にあたります。

## なぜ

NMI は画面、音、パッド、ポーズのルーチンを走らせます。そのあとポーズのバイトの下のビットを読みます。ビットが 1 ならタイマーを飛ばします。0 で、タイマーの親の制御（`TimerControl`）が 0 なら `DecTimers` を走らせます。位相を 1 減らし、0 からは周期のいちばん上にします。そのあとタイマーのループとモードのルーチンが来ます。ほかの命令は位相を番地で書きません。添字やポインタでの書き込みは、各命令の条件 `KeepsPhase` です。

`TaintRun` の抽象機械の 3 つの部分がフレームを追います。

* 歩き `A` はフレームの始まりから `DecTimers` の最初の命令（切れ目）までです。位相は `TaintRun` のカウンタとして追います。位相に書く命令があると歩きは失敗します。ポーズのバイトの下のビットと、タイマーの親の制御（0）は、始めにわかっています。切れ目に来ない道はポーズのフレームです。フレームの終わりまで進み、そこで位相がまだ追われていて、下のビットが 1 とわかっていなければなりません。
* 切れ目で、位相を 21 の値に分けます。各値 `p` から、タイマーのコードはタイマーのループ（`BPL` の行き先）まで進みます。そこで位相が `(p + 20) % 21` とわかっていなければなりません。
* 歩き `B` はタイマーのループからフレームの終わりまでです。位相を新しい値からまた追います。終わりで、位相がまだ追われていて、ポーズのバイトの下のビットが 0 とわかっていなければなりません。

タイマーの親の制御について。ゲームはこれを番地で書くのは、タイマーを動かすとき（0）、プレイヤーの状態を変えるためにタイマーを止めるとき（ルーチンのバイトの書き込みのすぐあと）、0 でないときの NMI の中だけです。操作の 3 バイトへの書き込みで道を止める `FrameKeep` の歩き（`FrameKeep.Frames.noStore`）に、見るバイトを 1 つ足すと、これは 0 のままです（`tcCheck`）。

## 定理

`m` はフレームが始まるときの機械、`frame(m, i)` は終わるときの機械です。`trace(m, i, j)` は `j` 命令のあとの機械です。

```
φ(m)      :=  m の位相: DecTimers の DEC が減らすバイト                               (PhaseFrame.phaseI)
tc(m)     :=  m のタイマーの親の制御                                                (PhaseFrame.tcI)
U(m)      :=  m のポーズのバイトの下のビットが 0                                     (FrameKeep.Unpaused)
next(p)   :=  (p + 20) % 21                                                          (時計の規則、CastleToLevel.Step)

PhaseRule(m, m')  :=  ( ¬U(m') ∧ φ(m') = φ(m) )  ∨  ( U(m') ∧ φ(m') = next(φ(m)) )

KeepsPhase(m)     :=  m の添字やポインタでの RAM への書き込みは、φ にも tc にも書かない
guardPh           :=  φ と tc も守る FrameKeep.guardE;   CleanK(guardE) ∧ KeepsPhase  ⟹  CleanK(guardPh)      (cleanPh_of)

phase_frame  :  phaseCheck,  StartK(m),  tc(m) = 0,  φ(m) ≤ 20,  ∀ j, CleanK(guardPh, trace(m, i, j))
                ⟹  PhaseRule(m, frame(m, i))
tc_frame     :  tcCheck,  StartK(m),  Watched(m),  tc(m) = 0,  ∀ j, CleanK(guardPh, trace(m, i, j)),  ∀ j, 操作のバイトを番地で書かない
                ⟹  tc(frame(m, i)) = 0
frames_phase :  keepCheckOf, phaseCheck, tcCheck,  K はフレーム a からの FrameKeep.Frames,  StartK(seq 0),  Watched(seq 0),  tc(S.seq a) = 0,  φ(S.seq a) ≤ 20,
                ∀ n < ix(g), ∀ j,  KeepsPhase(trace(S.seq(a + n), S.inp(a + n), j))
                ⟹  ∀ n < ix(g),  tc(S.seq(a + n)) = 0  ∧  φ(S.seq(a + n)) ≤ 20  ∧  PhaseRule(S.seq(a + n), S.seq(a + n + 1))
```

`ix(g)` は触るフレームの終わりです。フレーム `a` から `a + ix(g) − 1` が `FrameKeep.Frames` のフレームです。`frames_phase` は `n` の帰納法です。各フレームは `Frames.all_start` で操作中に始まります。`cleanE` と `KeepsPhase` から `CleanK(guardPh)` が出ます。`tc_frame` が `tc = 0` を次のフレームに運び（`noStore` を使う）、`PhaseRule` が `φ ≤ 20` を保ちます。

どれも `Theorems/PhaseFrame.lean` にあります。非公開の証明（`Proof/PhaseFrame.lean`）は、ROM で `phaseCheck` と `tcCheck` を `native_decide` で確かめ、`φ` がタイトルの名前の `IntervalTimerControl` であること（`Route.PhaseName`）も確かめます。

## 歩き

| 部分 | 始まり | 表の状態 |
|---|---|---|
| 歩き `A`、`DecTimers` まで | 4（下のビット 0 か 1、フレームの早いか遅いか） | 15,554。切れ目の状態は 12 |
| タイマーのコード | 12 × 21 | なし |
| 歩き `B`、タイマーのループから | 252 | 38,386 |
| `tcCheck` の歩き | 2 | `FrameKeep` の探索 |

ネイティブで、`phaseCheck` は探索も入れて 3.0 秒、`tcCheck` は 0.3 秒です。`Proof.PhaseFrame` のビルドは約 4 秒です。

## 本物の走りで

`phase-frames-check FM2` は、フレーム `b₂` が始まるときの機械から城に入るときまで走らせます。触るフレームまで（フレームが始まるときにプレイヤーのルーチン）の各フレームで、各命令の `KeepsPhase`、フレームが始まるときの `tc = 0`、`PhaseRule` を確かめます。触るフレームのあとは、城に入る走りで `PhaseRule` を確かめます。

| 走り | 走りの数 | 城に入った数 | 触るフレームまでのフレーム（ポーズで終わるもの） | 命令 | そのあと城までのフレーム（ポーズで終わるもの） | 失敗 |
|---|---|---|---|---|---|---|
| 動画 | 1 | 1 | 240 (0) | 1,203,506 | 126 (0) | 0 |
| `b₂` から城まで 1 フレームおきに、45 か 61 フレームのポーズ | 368 | 368 | 101,040 (12,720) | 466,482,861 | 53,046 (6,678) | 0 |
| 動画のフレーム `b₂` から `b₂ + 199` のどれかから、ランダムな入力、ランダムな Start | 100 | 19 | 58,172 (20,105) | 217,296,349 | 17,823 (6,229) | 0 |

「失敗」は、`KeepsPhase`、`tc = 0`、操作のときの `φ ≤ 20`、触るフレームの前とあとの `PhaseRule` の失敗の数です。操作のとき、どの走りでも `φ` は 20 以下です。

城に入らない 81 のランダムな走りでは、操作から離れたあと（死んだあと）の 4,650 フレームが `PhaseRule` に従わず、そういうフレームのうち 7,989 で、フレームが始まるときに `tc` が 0 ではありません。これらは `Route.Run` の走りではなく、これらのフレームには何も求めません。

動画で、フレーム 0 から時計の種類を機械から読み（`CastleToLevel.kindOf`）、位相を `read₀` のものにすると、城に入るまでの 1,219 フレームすべてで、時計の位相は機械の位相です。

## 証明していないこと

* 各命令の `KeepsPhase`。上で測りました。
* 地上の操作（`b₂`）での `tc = 0`。1 つの状態の条件で、測りました。
* 触るフレームのあと、城に入るまでのフレーム。そこではルーチンがプレイヤーのものでなく、それらのフレームを追う歩きはありません。そこでの `PhaseRule` は `Run.lagUp_of` の仮定 `hA` です（[城をつなぐ](0-5-2-1-CastleJoin-ja.md)）。上で測りました。
* 時計のつながり: 地上の各フレームで、時計の位相が機械の位相であること（`Run.PhaseUp`）。[城をつなぐ](0-5-2-1-CastleJoin-ja.md) を見てください。

**ファイル.** `Theorems/PhaseFrame.lean`（`phaseCheck`、`tcCheck`、`KeepsPhase`、`PhaseRule`、`phase_frame`、`tc_frame`、`frames_phase`）。

**再現.**
```
.lake/build/bin/smbrta phase-frame-check            # 探索と 2 つのチェック、プログラムとして（約 7 秒）
.lake/build/bin/smbrta phase-frames-check FM2       # 本物の走りでの条件（約 115 秒）
cd ../proof && leanman build Proof.PhaseFrame        # ROM でのチェック、ネイティブで（約 5 秒）
```
