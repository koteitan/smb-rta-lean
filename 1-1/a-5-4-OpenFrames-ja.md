[← Back](README-ja.md) | [English](a-5-4-OpenFrames.md) | [Japanese](a-5-4-OpenFrames-ja.md)

# 本物のフレームでの出だし

**主張.** 本物のフレームでの出だしの上限は、もう `Route.Pipe` のフィールドではありません。

* `openP`（フレーム `N` までの位置は `P₀ + D` 以下）は要りません。操作のときの位置は `P₀` で、タイトルで Start を押したことから読みます（`Run.pipePos`）。フレーム `N` までは
  各フレームが動くのは `16·v_top` 以下です。フレーム `E ≤ N` で入ることは、土管の左なのでできません（`PipeFrames.no_entry_of_start`）。
* `openB`（フレーム `N` の終わりの位置は `P₀ + D` 以下）は定理です（`Run.pipeOpenB`）。最初の `N` フレームの各フレームについての条件から出ます。そのフレームは
  [出だし](a-3-Opening-ja.md) のモデルの 1 歩である（新しいフィールド `opening`）。

`N = 32`、`D = 9744`（1/256 px）、`v_top` は走りの最高速（2.5 px/フレーム）です。`fm(t)` は数えるフレーム `t` が始まるときの機械、`hs(t) = startHS(fm t)` はその横の状態
（速さ、端数、向き、動く向き、走りの速さ）、`P(t)` はその位置、`v(s)` は状態 `s` の符号つきの速さです。`E` は入るフレームです。`fr(t)` はフレーム `t` の `Frame` です
（[土管までのフレーム](a-5-5-PipeFrames-ja.md)）。`lens(|v|) = (L_tap, L_hold)` は、ジャンプの始まりから着地のフレームまでの長さで、A を 1 フレームだけ押したときと押し続けたときの
ものです。跳ぶときの速さごとにエミュレータで測りました。

```
OpenRun(air)  :  air(1) = 0,  そして t ∈ [1, N],  t < E  の各 t で  ∃ i ∈ inputsN:
                   valid(air t, i)  ∧  air(t + 1) ∈ modes(lens, hs t, air t, i)
                   ∧  hs(t + 1) = hstep(hs t, i)  ∧  P(t + 1) = P(t) + 16·v(hs(t + 1))
valid(r, i)   :=  (r = 0  ∧  i は地面で始まる)  ∨  (r > 0  ∧  i は空中で始まり、跳び始めない)
modes         :=  地面で跳び始める: [L_tap(|v|) − 1, L_hold(|v|) − 1];  地面: {0};  空中: {r − 1}

OpenRun.reach      :  OpenRun,  hs(1) = startHS(m₀)   →   ∀ k ≤ N,  1 + k ≤ E  →  Reach(start, k, ((hs(1 + k), air(1 + k)), P(1 + k) − P(1)))
OpenRun.endB       :  OpenRun,  hs(1) = startHS(m₀),  (∀ k ≤ N,  Reach(start, k, u)  →  dist(u) ≤ D),  N < E   →   P(N + 1) ≤ P(1) + D
OpenRun.openB      :  同じ前提,  Reads,  P(1) = P(m₀),  1 ≤ N   →   N < E  →  fr(N).P' ≤ P(m₀) + D

no_entry_of_start  :  16 ≤ v_top,  1 ≤ N,  2·N ≤ T,  (∀ t, Enter t → L ≤ fr(t).P₂),  fr(1).P ≤ B,  (N < E → fr(N).P' ≤ B),
                      Reads,  v(fm 1) = 0,  B + 16·v_top·(T − N) < L,  Enter E,  1 ≤ E   →   T < E
Run.pipeP1         :  fr(1).P = P(m₀)                            （title_check、title_pos_check、フレームの確認）
Run.pipeHS         :  hs(1) = startHS(m₀)                        （title_check、title_pos_check）
Run.pipeOpenB      :  N < E  →  fr(N).P' ≤ P(m₀) + D             （opening と非公開の opening から）
```

`Reach(start, k, u)` は `Opening` のモデルです（`Opening.succ` の `Cert.Reach`）。上限 `∀ k ≤ 32, Reach(start, k, u) → dist(u) ≤ 9744` は非公開の `opening` です
（探索、約 4 秒）。`title_pos_check` は ROM での確認で、非公開の `Proof/LagPause.lean` にあります（ネイティブで約 1.6 秒）。
ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/OpenFrames.lean`、`Theorems/PipeFrames.lean` の `no_entry_of_start`、`pos_le`、`Theorems/StartRun.lean` の `titlePosCheck`、`Begin.pos₁`、`Begin.hs₁`、
`Theorems/Route.lean` の `Pipe.opening`、`Run.pipePos`、`Run.pipeHS`、`Run.pipeP1`、`Run.pipeOpenB`、非公開の `Proof/LagPause.lean`、`Proof/Opening.lean`、`Proof/PipeWrites.lean`。

## しくみ

* **フレームだけから出ること.** `Frame` と操作のときの速さ 0 からは、フレーム 32 の終わりは `P₀ + 16·v_top·32 = P₀ + 20480` 以下です。1 フレームの加速の上限
  （`V' ≤ max(V, 0) + a_max`、`a_max = 456`、速さの単位の 1/256）を使うと `P₀ + 14528` 以下です。出だしには `P₀ + 9744` が要ります。なので `openB` は `Frame` からは出ません。
  出だしのモデル（B なしの地面での上限、ジャンプの長さ）が要ります。
* **`openP`.** `E ≤ N` なら: `fr(E).P₂ ≤ fr(E).P + 16·v_top ≤ P(1) + 16·v_top·E`（`pos_le`）、そして `P(1) = P₀` です。`2·N ≤ T` なので、これは
  `P₀ + D + 16·v_top·(T − N) < L` 以下で、入れません。`E > N` なら、前と同じくフレーム `N` の終わりの上限を使います。
* **`openB`.** `k` についての帰納法です。数えるフレーム `1 + k` の状態は、モデルが `k` 歩で着く状態です（`OpenRun.reach`）。フレーム `t` から `t + 1` への 1 歩は、フィールド `step`
  により `Opening.succ` の後者です。始まりは `start(m₀)` です。`hs(1) = startHS(m₀)`、`air(1) = 0` だからです。モデルの距離は `P(t) − P(1)` です。非公開の `opening` が
  `k = N` でそれを `D` 以下にします。
* **操作のときの状態.** `title_pos_check` は、`title_ctl_check` と同じく、タイトルの集合の近い状態のどれからもどの入力でもフレーム 0 を追います。操作できる終わりのそれぞれで、
  位置の 3 バイトと横の状態の 5 バイトが `m₀` の値でわかっていることを確かめます。

## 本物のフレームで確かめたこと

プログラムです（`open-frames-check`）。操作のときの機械から最初の 32 の数えるフレームを動かします（インターバルタイマーが動かないフレームは飛ばします）。`air(t)` は
`Player_State` から読みます。地面なら 0、そうでなければ地面で始まる最初のフレームまでのフレーム数です。各フレームで、`step` の 4 つの条件を満たす `inputsN` の入力 `i` を探します。

| 走り | フレーム | 跳び始め | モデルの 1 歩でない | `P(33) − P(1)` |
|---|---|---|---|---|
| TAS | 32 | 2 | 0 | 9744 |
| 操作のときからの自分の入力、Start あり（300 回） | 9,600 | 580 | 0 | 最大 8448 |

* TAS では、操作のときの横の状態は `m₀` のもので、位置は `P₀` です（`lag-pause-check` でも）。

## 前提（Lean では証明していない）

* **`opening`**: 最初の 32 の数えるフレームのどれもモデルの 1 歩である。1 フレームごとの条件です。[出だし](a-3-Opening-ja.md) がモデルについて仮定していたことを含みます。
  開けた平らな地面で、空中はジャンプのあいだだけ（項目 1-1-a-5-6）。ジャンプの長さは跳ぶときの速さだけで決まり、`L_tap` と `L_hold` のあいだにある（項目 1-1-a-5-7）。
  フレームの横の部分は `hstep` で、位置は `16·v` だけ動く（壁や画面の端はない）。2 つの数えるフレームのあいだの数えないフレーム（ポーズ）は、その 1 歩の中に入ります。
* **証明していないこと:** フレーム 368 で入れること（前と同じ）。

**ファイル.** `Theorems/OpenFrames.lean`、`Theorems/PipeFrames.lean`、`Theorems/StartRun.lean`、`Theorems/Route.lean`、非公開の `Proof/LagPause.lean`、`Proof/Opening.lean`。

**再現.**
```
.lake/build/bin/smbrta open-frames-check FM2 300    # 最初の 32 フレームをモデルの 1 歩として、TAS と自分の入力で、約 30 秒
.lake/build/bin/smbrta open-check 32 9744           # モデルの上限（true）
```
