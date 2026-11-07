[← Back](README-ja.md) | [English](d-2-2-SideChangeBound.md) | [Japanese](d-2-2-SideChangeBound-ja.md)

# 地上への切り替えのはじめのフレームを 1 フレームから出す

**主張.** これは部分的な結果です。1 つの状態についての条件を満たす機械は、入ったあと 160 フレームのあいだ、どの入力でも操作できません。証明は 1 フレームだけを見ます。160 フレームは式で出ます。土管のタイマーのあとのフレームは、ここでは証明していません。本物の走りが条件を満たすことも証明していません。

`m₀`、`run`、`ctl`、`0^k`、`E` は[地上への切り替えの長さを決めるもの](d-2-1-SideTransitionAll-ja.md)と同じです。`w[..j]` は `w` のはじめの `j` 個の入力です。`timer(m)` は `ChangeAreaTimer` です。`frame(m, i)` は入力 `i` の本物の 1 フレームです。

**条件.** `EntryCond(M)` は、入るフレームの終わりの状態 `M` についての条件です。

* フレームは待ちの繰り返しの中で終わっています。プログラムカウンタとスタックポインタは `E` と同じです。ドットは 9 以下です。vblank と NMI のフラグはドットに合っています。スプライト 0 のフラグは立っています。PPU 制御で NMI はオンです。コントローラはストローブ中ではありません。
* `timer(M) ≥ 160`。これで、画面が別のページにある状態（174 フレーム）と、入るフレームがタイマーを書かなかった状態を除きます。それらのタイマーはもっと小さいです。
* `K` の 82 バイトは `E` と同じ値です。下に挙げます。
* 画面のバッファは空か、色の回転のレコードが 1 つ入っています。2 つ目の場合は 3 バイト増えます。この 2 つは、`E` と、その 6 フレームあとから取ります。

ほかのバイトは何でもかまいません。マリオの `x`、速さ、大きさ、状態、コイン、スコア、ゲームタイマーの数字、ポーズのバイト、フレームカウンタ、乱数、音楽と効果音の残りの状態、スプライト、ブロックバッファ、一時的なバイトです。

**リスト `K`**（名前）:

| まとまり | バイト |
|---|---|
| モード | `OperMode`、`OperMode_Task`、`GameEngineSubroutine`、`ScreenRoutineTask`、`DisableScreenFlag`、`WorldNumber`、`AreaType`、`SecondaryHardMode` |
| マリオ | `Player_State`、`Player_Y_HighPos`、`Player_Y_Position`、`Player_SprDataOffset`、`JumpspringAnimCtrl` |
| 物 | `Enemy_Flag`（6）、`Enemy_ID+5`、`Fireball_State`（2）、`Block_State`（2）、`Block_RepFlag`（2）、`Misc_State`（9）、`FloateyNum_Timer`（6）、`VineFlagOffset`、`Cannon_PageLoc`（6）、`Cannon_X_Position`（6）、`Cannon_Y_Position`（4）、`StarInvincibleTimer` |
| 面の敵 | `EnemyData`（2）、`EnemyDataOffset`、`EnemyObjectPageLoc`、`EnemyFrenzyBuffer`、`EnemyFrenzyQueue` |
| 画面 | `ScreenRight_PageLoc`、`ScreenRight_X_Pos`、`ScrollLock`、`ScrollThirtyTwo`、`AreaParserTaskNum`、`VRAM_Buffer_AddrCtrl`、`VRAM_Buffer1_Offset`、`VRAM_Buffer1` |
| 音楽 | `AreaMusicBuffer`、`EventMusicBuffer`、`MusicData`（2）、`MusicOffset_Square1`、`NoiseSoundBuffer`、`AreaMusicQueue`、`EventMusicQueue`、`NoiseSoundQueue` |

**土管のあいだの状態.** `During(m)` は、`m` が同じ `K` の抽象状態に含まれることです。1 つの形ではタイマーは 2 以上で、値はわかりません。もう 1 つの形ではタイマーは 1 とわかっています。`Exit(m)` は、`m` の `OperMode_Task`、`ScreenRoutineTask`、`GameEngineSubroutine`、`DisableScreenFlag` が `T = run(E, 0^160)` と同じことです。

**数 `left`.** ゲームコアで土管のルーチンが動いているあいだは `left(m) = timer(m) + 122` です。そのほかでは 122 行の表から読みます。表は `T` を入力なしで動かして作ります。各行はキーと残りのフレーム数です。表にないキーは `left = 0` です。これは [1 フレームずつの事実から出す下限](b-2-2-PipeChangeBound-ja.md)の `left` と同じ形で、表が違います。

```
during       :  ∀ M,  EntryCond(M) → During(M)
step         :  ∀ m, During(m) → ∀ i :
                  ( During(frame(m, i)) ∧ timer(m) ≤ timer(frame(m, i)) + 1 )  ∨  ( timer(m) = 1 ∧ Exit(frame(m, i)) )
noFirst      :  ∀ M,  EntryCond(M) → ∀ w, ∀ j ≤ |w|, j ≤ 160 → ¬ctl(run(M, w[..j]))
fall         :  ∀ m, During(m) → ∀ i,  left(m) ≤ left(frame(m, i)) + 1
atEntry      :  ∀ M,  EntryCond(M) → 282 ≤ left(M)
atControl    :  ∀ m,  ctl(m) → left(m) = 0
noAll        :  ∀ M,  EntryCond(M) → ∀ w,
                  (∀ j < |w|, ¬During(run(M, w[..j])) → left(run(M, w[..j])) ≤ left(run(M, w[..j+1])) + 1)
                  → ∀ j ≤ |w|, j < 282 → ¬ctl(run(M, w[..j]))
no_input     :  ∀ M,  EntryCond(M) → ∀ k, 1 ≤ k ≤ 160 → ¬ctl(run(M, 0^k))
ChangeRun.bound :  `ChangeRun` のフィールドを持つ走りについて :  cnt(a) + 282 ≤ cnt(b)
```

`no_input` は `SideTransitionAll.every_entry` の `(H1)` です。`(H2)` と `(H3)` は出ません。ポーズのバイトが自由なので、タイマーはフレーム数より遅れることがあり、条件はフレーム 160 の状態の位置を決めません。下限には要りません。

Lean: `Theorems/SideChangeBound.lean`（`frame_of_walk`、`inv_step`、`inv_seq`、`state_seq`、`fall_of_inv`、`no_control_first`、`no_control_all`、`inv_of_entry`、`entryCond_of_ok`、`Statement`、`statement_of_check`、`Statement.no_input`、`change_counted`、`ChangeRun`、`ChangeRun.bound`）、非公開の `side_bound_checks`（`native_decide`）、`side_bound`、`side_no_control`、`side_change_bound`。ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

## しくみ

**抽象機械.** [一部のバイトがわからない走り](b-2-3-TaintRun-ja.md)の機械を、このファイルに写して 3 つ変えました。パッドは、わからないビットのあるバイトです。土管のタイマーは追うカウンタです。値はわかりませんが、`Sim` は、このフレームで高々 1 減ったことを言います。それを書いてよいのは、その `DEC` だけです。あるバイトは、いくつかのビットで分けて読めます。フレームカウンタは下の 3 ビットで分けて読みます。`ColorRotation` がそれを添字に使うからです。

**1 フレーム.** 開始状態から抽象機械で 1 フレーム進めると、終わりは開始状態だけです。ですから土管のどのフレームも `During` のままです。タイマーが 1 のときは、終わりは `During`（ポーズ）か `Exit` です。確認はタイマーが自由な場合に 106,824 個、タイマーが 1 の場合に 52,701 個の抽象ステップを追います。表は 4,584 個と 2,519 個です。プログラムで約 1 秒、非公開の証明のビルドで約 33 秒です。`Theorems` はあらかじめコンパイルされないからです。

**ここで閉じる理由.** 土管のルーチンでは、面との当たり判定（`PlayerBGCollision` はこのルーチンで抜けます）もゲームタイマー（`RunGameTimer` も抜けます）も動きません。ですからタイマーは書き直されず、このフレームでは急ぎの音楽は始まりません。部屋の曲には矩形波 1 の部分がありません（`MusicOffset_Square1` がそれを示します）。ですから 0 を読み続けて止まる繰り返しは動きません。

**物の枠が空のままである理由.** 確認は、`K` のもとで、挙げた物のバイトが土管のどのフレームでも変わらないことを示します。部屋の残りのフレームについては、コードと地図から読みました。これは Lean にしていません。部屋の敵のデータには、このページの敵がありません。`EnemyDataOffset` は、止まった画面の右端より先の項目で止まっています。ですから `ProcessEnemyData` は何も足しません。この面では敵の群れのキューは立ちません。この面に大砲はないので撃ちません。ブロックバッファにアイテムの入ったブロックはありません。ファイアボールにはパワーアップが 2 つ要りますが、1-1 のこの土管より前のパワーアップは 1 つです。

**入力.** ポーズはタイマーを止めます。パッドとポーズのバイトがわからないので、これも含みます。本物の入る状態で最初のフレームから `Start` を押し続けると、1,500 フレームのあいだ操作できません。

**この方法で届かないところ.** 土管のあとのフレームは RAM を消し、その繰り返しの中でフレームが終わります。抽象機械は、待ちの繰り返しの外で終わるフレームで失敗します。ですから最後の 122 フレームは証明していません。[項目 1-1-d-2-3](../README-ja.md) は残ります。

## 測ったけれど定理にしていないこと

プログラムで、次の入る状態から本物のフレームを動かしました。

| 入る状態 | 個数 | 条件を満たす |
|---|---|---|
| `E` と TAS の入る状態 | 2 | 2 |
| `side-all-real` の本物の入る状態 | 42 | 42 |
| 部屋までの乱数の走りと、部屋での乱数の操作 | 21 | 21 |
| 同じ。1-1 の開始で大きいマリオに書き換え（入るとき 5 個は大きいまま） | 7 | 7 |
| 同じ。部屋でゲームタイマーの数字を 100 の近くに書き換え | 5 | 4 |
| 同じ。1-1 の開始でファイアマリオに書き換え | 3 | 0 |

* 条件を満たす 76 個のそれぞれから、入力なし、`Start` なしの乱数入力、乱数入力、`Start` を押し続ける入力で動かしました。合計 199,995 フレームです。`left` が 2 以上減るフレームはありません。操作できるのは `left = 0` のときだけです。どの入る状態でも `left = 282` です。いちばん短い切り替えは 282 フレームです。`Start` を押し続けると、どの走りも 1,500 フレームのあいだ操作できません。
* ゲームタイマーが 100 の近くで条件を満たさない 1 個は、急ぎの音楽が鳴っています。`AreaMusicBuffer`、`EventMusicBuffer`、`MusicData`、`MusicOffset_Square1` が違います。ファイアマリオの 3 個は `Fireball_State` が違います。
* 切り替えが短くなる書き換えた状態（174、174、127 フレーム）は条件を満たしません。
* プログラムの 44 個の入る状態では、1 つの走りで、タイマーが動かず `left` が減るフレームは 0 個（`Start` を押し続ける）か 1 個です。

## 前提（Lean では証明していない）

* 本物の走りの入る状態での `EntryCond`。`K` のバイトは、測った走りでは部屋の中で一定です。すべての走りで成り立つことは、コードから読みました。特に:
  * `timer ≥ 160` は、入るフレームで画面が最初のページにあることです（[項目 1-1-d-2-4](../README-ja.md)）。
  * `Player_Y_Position` は床の値です。土管の口のタイルは床の高さにしかないからです。
  * 物のバイトは上のとおりです。`Block_State` には、入る直前にレンガが壊れないことが要ります。
  * 音楽のバイトは、急ぎの音楽が鳴っているあいだ、つまりゲームタイマーが 100 を過ぎた直後には成り立ちません。そのような走りは 1748 フレームよりずっと多く使っています。
* `During` の外のフレームで `left` が高々 1 しか減らないこと（`ChangeRun` の `fallAfter`、`noAll` の仮定）。最後の 122 フレームです。
* `lag` のフレームで `left` が減らないこと（`ChangeRun` の `lagKeeps`）。測った本物の走りでは、タイマーが動かず `left` が減るフレームは、切り替えの `setup` のフレーム 1 つだけです。
* `Route` はこの定理をまだ使っていません。`ChangeRun` は、`change₂` を結論にするフィールドの一覧です。

**ファイル.** `Theorems/SideChangeBound.lean`、非公開の `Proof/SideChangeBound.lean`。

**再現.**
```
.lake/build/bin/smbrta side-bound-check FM2    # 確認、本物の入る状態での条件、本物のフレームでの left、約 30 秒
```
