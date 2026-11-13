[← Back](README-ja.md) | [English](d-3-4-2-SideChangeSound.md) | [Japanese](d-3-4-2-SideChangeSound-ja.md)

# 地上への切り替えを、音のバイトを表にして

**主張.** 地上への切り替えの行は、音のルーチンの外で 38 個の音のバイトを忘れてよいです。そのバイトの状態の表を行のそばに運びます。これは ROM の確認つきで証明しました。この行では出口の条件が弱くなります。ポーズの音は鳴っていなくても、ポーズを解く音が鳴っていても、出口のフレームでポーズを解いていてもよいです（`QuietK`）。前は鳴っていないことが要りました（`Quiet`）。道筋は今 `QuietK` を仮定します。`chg.quiet₂`（1-1-d-3-4）は弱くなりました。測った 880 の出口のすべてで `QuietK` が成り立ちました。`Quiet` は 257 でした。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は `m` の入力 `i` での 1 フレームです。`Sim(S, m)` は抽象状態 `S` が `m` を覆うことです。`left`、`During2`、`Entry2`、`NoStart`、`TimerOK` は [地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md) のものです。`Ph`、`SIn`、`tsuccs`、`tframe_of_walk` は [CPU の 1 ステップが RAM を書く場所](d-3-4-1-StepWrites-ja.md) のものです。

## 出口の条件

`q`、`b`、`f`、`c` はバイト `PauseSoundQueue`、`PauseSoundBuffer`、`PauseModeFlag`、`Squ1_SfxLenCounter` です。`x` は出口の参照の機械です。`U` はポーズを解く音の値、`P` はポーズの音の値、`L` は音の長さです。この 3 つは ROM から記号で読みます（`UnpauseSfxValue`、`PauseSfxValue`、`PauseSfxLength`）。

```
QuietK(m)  :=  ( m[q] = x[q]  ∧  m[b] = x[b] )                                   鳴っていない。フラグは何でもよい
            ∨  ( m[q] = x[q]  ∧  m[b] = U  ∧  m[f] = U  ∧  1 ≤ m[c] ≤ L )         ポーズを解く音が鳴っている
            ∨  ( m[q] = U  ∧  m[b] = x[b]  ∧  m[f] = P )                          このフレームでポーズを解いた
Quiet(m)   :=  m[q] = x[q]  ∧  m[b] = x[b]
```

なので `Quiet(m) → QuietK(m)` です（`quietK_of_quiet`）。

## 行

行 `r` は、1 フレームの状態 `R(r)`、行の数 `left`、フレームの 2 つの表を持ちます。`T₀(r)` は音のルーチンを呼ぶ前、`T₁(r)` はルーチンから戻ったあとの表です。

```
CoveredS(r, m)  :=  ∃ S ∈ R(r),  Sim(S, m)  ∧  Ph(S, m)          Ph は T₀(r) と T₁(r) で
InvS(l, m)      :=  ∃ r ∈ l,  CoveredS(r, m)

chain_stepS  :  chainS(l)  ∧  InvS(l, m)  ∧  ( coreFrame(m) → NoStart(i) )
                →  left(m) = 0  ∨  ( InvS(l, frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
ctl_of_zeroS :  chainS(l)  ∧  zeroCtl(l)  ∧  InvS(l, m)  ∧  left(m) = 0  →  ctl(m)
```

`chainS(l)` は、行 `r` から次の行 `r'` への各フレームを確かめます。`r` の各状態と表の各状態から `tsuccs` で歩くと、`r'` の状態で終わります。フレームの終わりで成り立つ表（ルーチンが戻っていなければ `T₀(r)`、戻っていれば `T₁(r)`）は `T₀(r')` に入ります。つまりその各状態は `T₀(r')` のある状態に入ります。

## 命題

`InRowsK(m) := InvS(rowsK, m)` です。行 `rowsK` は、音のバイトを忘れた出口の状態から、`dg`（ゲームタイマーが 000 でない）つきで始まります。最初の表は `T_x` です。これは `QuietK` の 52 種類（鳴っていなくてフラグが 0 か、フラグの 1 つのビットが 1。ポーズを解く音の数が 1 から `L` まで。ポーズを解いた）に、出口のほかの音のバイトを加えたものです。`EndStatementK` は次のフィールドを持ちます。確認 `endCheckK` がそれを出します（`endStatementK_of_check`）。

```
entry         :  ∀ M,  Entry2(M) → Entry(M)
during        :  ∀ M,  Entry2(M) → During2(M)
toDuring      :  ∀ m,  During2(m) → During(m)
step          :  ∀ m, During2(m) → ∀ i :  During2(frame(m, i))
                   ∨  ( Exit(frame(m, i))  ∧  ( QuietK(frame(m, i)) ∧ TimerOK(frame(m, i)) → InRowsK(frame(m, i)) ) )
rows          :  ∀ m, InRowsK(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRowsK(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
zero          :  ∀ m,  InRowsK(m) ∧ left(m) = 0 → ctl(m)
duringLeft    :  ∀ m,  During2(m) → left(m) ≠ 0
pauseKeeps    :  ∀ m, During2(m) → ∀ i,  Paused(frame(m, i)) ∧ During2(frame(m, i)) → left(m) ≤ left(frame(m, i))
rowsNotPaused :  ∀ m,  InRowsK(m) → ¬Paused(m)
exitOff       :  ∀ m,  Exit(m) → ¬ctl(m)
```

**走り.** `EndRunK` は `SideChangeEnd.EndRun` のフィールドで、`Quiet` のかわりに `QuietK` を持ち、もう 1 つ、出口の `TimerOK`（`time`）を持ちます。`b` は入ったあと `a` からの最初の操作です（`hc`）。

```
EndRunK.bound  :  cnt(a) + 282 ≤ cnt(b)
EndRunK.first  :  hc  →  ∀ n ∈ [a, b),  left(seq n) ≠ 0
EndRunK.inRows :  hc  →  InRowsK(seq b)
EndRunK.start  :  hc  ∧  startCheckK  →  Start(PA, seq b)
EndRunK.atCtl' :  hc  ∧  ctlCheckK    →  AtCtl(seq b)
EndRunK.last   :  hc  →  a + 1 ≤ b  ∧  seq(b − 1) は行にある  ∧  left(seq(b − 1)) = 1
```

`Route` は `bound`、`start`、`atCtl'` を使います。`last` は `HurryStart` が行から読むものです。`HurryStart` はまだ使っていません。

Lean: `Theorems/SideChangeSound.lean`（`scan`、`SRow`、`rowsFromS`、`incl`、`finS`、`linkS`、`chainS`、`soundCtx`、`PauseIdx`、`pauseIdx`、`QuietK`、`kinds`、`tableAt`、`CoveredS`、`ph_next`、`link_frameS`、`InvS`、`chain_stepS`、`invL_of_invS`、`ctl_of_zeroS`、`inv_headS`、`bit_of_ne`、`kinds_of_quiet`、`quietK_of_quiet`、`InRowsK`、`endCheckL`、`endCheckK`、`EndStatementK`、`endStatementK_of_check`、`EndRunK`、`st_stepK`、`EndRunK.bound`、`EndRunK.way`、`EndRunK.first`、`EndRunK.inRows`、`EndRunK.last`、`startCheckK`、`ctlCheckK`、`sideCheckK`、`EndRunK.start`、`EndRunK.atCtl'`）、非公開の `side_sound_checks`（`native_decide`、`Proof/Route.lean` の中）、`side_sound`。公開のファイルにゲームのデータはありません。

## しくみ

**1 フレーム.** 歩きは `tsuccs` での `twalk` です。音のルーチンの外では音のバイトはわかりません。呼ぶところで状態を `T₀(r)` で分け、バイトがわかったままルーチンを歩きます。戻るところでバイトは `T₁(r)` に入らなければならず、そこで忘れます。ルーチンの外の 1 ステップが音のバイトを書くなら、表は閉じたままでなければなりません（`writeOK`）。`tframe_of_walk` がフレームを出します。その終わりで、成り立つ表が `T₀(r')` に入るという確認によって、`Ph` は次の行に移ります（`ph_next`）。

**表.** 表は確認がフレームごとに作ります。戻るところで何も確かめない探索（`scan`）が、呼ぶ前の音のバイトへの書き込み、戻るところのバイト、戻ったあとの書き込みを出します。書き込みは表に合わせます（`joinUnder`）。同じ探索の状態が歩きの表になるので、各フレームの探索は 1 回です（呼ぶ前に書き込みがあるときは 2 回）。戻るところの状態は分けたままにします。種類ごとに合わせると、曲の頭を探す音楽のルーチンが 0 かもしれないバイトで回り、終わりません。

**フラグは表の中.** `SideChangeEnd` では、音のポーズのフラグのために行の組が 2 つ、時間の行の組が 9 つ要りました。ここではフラグは音のバイトなので、その場合分けは表の状態です。1 組の行で 52 種類すべてに足ります。

**出口.** 土管を出るフレームは `baseK` の状態で終わります。これは出口のバイトを知っていて、ポーズの音の 2 バイトは知りません（バイトを求めない土管のフレームの確認、`[]` での `duringCheck`）。音のバイトを忘れて `dg` をつけると、最初の行の状態です。`QuietK` から種類が出て（`kinds_of_quiet`）、状態の知っているバイトから出口のほかの音のバイトが出ます（`soundLe`）。なので最初の表で `Ph` が成り立ちます。

**確認の大きさ.** 行は 123、状態は 2,280、表の状態は 76,522、いちばん大きい表は 507 状態です。行を作るのはネイティブで約 20 秒、その歩きは約 17 秒です。確認 `endCheckK` 全体はプログラムで約 39 秒です。これは数秒より長いです。道筋では、3 つの確認のために行を 1 回だけ作ります（`sideCheckK`）。

## 測ったが定理でないもの

プログラム: `sound-rows-real FM2 20`。`Entry2` を満たす 44 の入るとき（参照の入るとき、ムービーの入るとき、42 の本物の入るとき）から 20 回ずつ、土管のフレームで Start をランダムに押し、そのあと操作できるまで Start なし。

| 出口で | 走り |
|---|---|
| すべて | 880 |
| `exitKnownK` のバイトで `ExitCond` | 880 |
| `QuietK` | 880 |
| `Quiet` | 257 |
| ゲームタイマーが 000 でない | 880 |

これらの走りでは、出口のあと各フレームで `left` はちょうど 1 減り、`left` が 0 のところでちょうど操作できます。入ってから操作できるまで 375 から 598 フレームでした。

## 道筋で変わったもの

* `Route.Changes` を分けました。`ChangesBase` は `quiet₂` 以外のすべてのフィールドを持ちます。`ChangesK` は `QuietK` の `quiet₂` を加え、`Run.chg` は `ChangesK` です。`Changes` は `Quiet` の古い `quiet₂` を加えます。`HurryStart` と `HurryMusic` はまだこれを読みます。`Changes.toK` は `Changes` を `ChangesK` にします。
* `Run.change₂`、`Run.start`、`Run.atCtl₀`、`level_ge_of_parts` は、`SideChangeEnd.EndStatement`（と `startCheck`、`ctlCheck`）のかわりに `SideChangeSound.EndStatementK`（と `startCheckK`、`ctlCheckK`）をとります。
* 切り替えの長さ（`Run.change₂`）は `chg.time₂` も使うようになりました。行が時間の行だからです。`time₂` はもとからフィールドでした。

## 仮定（Lean で証明していないもの）

* 出口での `QuietK`（`chg.quiet₂`、1-1-d-3-4）。証明するには土管のフレームにも表が要ります。そこでは Start が許されるので、ポーズの音の状態を入るときから運ばなければなりません。
* `NoStart`（`chg.noStart₂`、1-1-d-3-3）: 土管のあと、ゲームコアのフレームで Start を押さない。ポーズしたフレームは `left` を 1 減らさず、行は `left` の値ごとに 1 つです。まだです。
* ほかは [地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md) のとおりです: `Entry2`、`lagPaused`、`TimerOK`。

**ファイル.** `Theorems/SideChangeSound.lean`。非公開の確認は `Proof/Route.lean`、音のルーチンの場所は `Proof/SideChangeSound.lean` にあります（`Main.lean` の `genSideSound`）。記号 `PauseSfxValue`、`UnpauseSfxValue`、`PauseSfxLength` は `tools/smb-symbols.txt` にあります。

**再現.**
```
.lake/build/bin/smbrta sound-rows-check          # 行、その確認、endCheckK。約 80 秒
.lake/build/bin/smbrta sound-rows-real FM2 20    # 880 の本物の走りでの条件。約 2.5 分
```
