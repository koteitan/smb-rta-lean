[← Back](README-ja.md) | [English](c-7-4-4-StoredClean.md) | [Japanese](c-7-4-4-StoredClean-ja.md)

# モデルに従うフレームと古い保存された速さのあとの保存された速さ: `ab_run`、`ab_early` を狭める

[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `ab_run` と `ab_early`（項目 1-1-c-7-4 と 1-1-c-7-6）は、モデルに従わないフレームが読む保存された速さを押さえるものです。ラウンド 32（[止まったあとの保存された速さ](c-7-4-3-AbsKeep-ja.md)）は、1 つ前のフレームが止まり、そのプレイヤーのルーチンに `AtCtrl` の状態で来る場合を証明しました。このラウンドでは、さらに 3 つの場合を証明します。

1. 1 つ前のフレームがモデルに従う: その終わりで保存された速さは `|v|` です（`ab_cleanW`）。
2. 1 つ前のフレームが止まり、そのプレイヤーのルーチンに古い保存された速さで来る: その始めの速さは 0 で、その摩擦が残すのは多くて加える量 1 つと端数です（`ab_stale`）。ただし、空中で左も右も押していないときは別です。
3. `RoomCore.stop_run` は壁にぶつからないときだけ使われるので、`C + 37` からだけ求めます。すると `ab_early` を使うのは `RoomCore.ab_of` だけで、そこでは `C + 34` での `AtCtrl` の状態の止まりはすでに場合の 1 つです。

それで、どちらのフィールドも、1 つ前のフレームがプレイヤーのルーチンに、保存された速さが `|v|` で押している向きが隠された状態で来るか、空中で左も右も押さずに古い保存された速さで来るときだけ求めます。

## 命題

`fm(n)` はフレーム `n + 1` が始まる機械、`fe(n)` はフレーム `n` の終わりの機械、`T(n)` はフレーム `n + 1` のプレイヤーのルーチンでの機械です。`xa` は保存された速さ `Player_XSpeedAbsolute`、`v` は速さ `Player_X_Speed`、`|x|` は符号つきの数として見たバイトの大きさです。`PlayerSubs` は移動の終わりです。`R = RunSpeedMin`（1 フレームに 1.75 px）、`A = AirFastSpeed`（1 フレームに 1.5625 px）。`amax` は摩擦で加える量のいちばん大きいもので、速さの単位の 1/256 で数えます（1 フレームに約 0.11 px）。

数の側では: `hs(n)`、`v(n)`、`rs(n)`、`st(n)` はフレーム `n` の終わりの横の状態、速さ、`RunningSpeed`、状態です。`inp(n)` はフレーム `n` の入力、`ab(n)` はフレーム `n + 1` がプレイヤーのルーチンで読む保存された速さ、`Follow(n)` はフレーム `n + 1` が `hstep` に従うことです。`CleanW(n)`、`ReadW(n)`: フレーム `n + 1` についてのフィールド `clean` の 2 つの場合（モデルに従う、止まる）。`AtCtrl(n)`: `T(n)` が `FrameModel.AtCtrl` の状態（`xa = |v|` で、押している向きが当たりのビットで隠されていない）。`Stale(n)`: `T(n)` で `xa ≠ |v|`。`AirNoSide(n)`: `T(n)` のモデルの場合で、空中にいて、左も右も押していない（`FrameModel.stOf ≠ 0`、`FrameModel.lrOf = 0`）。部屋の数は `fall = 34`、`hitF = 37`、`runF = 40` です。

```
FrameModel.stored_pathM（証明、StoredClean）:
  R で AtCtrl,  速さは TopSpeed の範囲,  storedOK,  storedM
    →   ∃ k,  (stepN k R).pc = PlayerSubs  ∧  そこで xa = |v|

FrameModel.stored_pathF（証明、StoredClean）:
  R で AtFrame,  storedOK
    →   ∃ k,  (stepN k R).pc = PlayerSubs  ∧  (そこで xa = |v|  ∨  (AirNoSide  ∧  そこでの xa, v は R のもの))

RoomRun.end_cleanW（証明）:   C ≤ n,  n + 1 < t0,  CleanW(n)   →   xa(fe(n + 1)) = |v(fe(n + 1))|
RoomRun.ab_cleanW（証明）:    C ≤ n,  n + 1 < t0,  CleanW(n)   →   ab(n + 1) = |v(n + 1)|

RoomRun.absOr0（証明）:       C ≤ n < t0   →   xa(fe(n)) = |v(fe(n))|  ∨  v(fe(n)) = 0

RoomRun.ab_stale（証明）:
  C ≤ n,  n + 1 < t0,  ReadW(n),  Stale(n)
    →   256 · ab(n + 1) ≤ 255 + amax   ∨   (AirNoSide(n)  ∧  ab(n + 1) = ab(n))

RoomCore.stop_run（証明: RoomRun.stop_run_of。いまは C + 37 から）:
  C + 37 ≤ n + 1,  n < C + 40,  rs(n) = 0,  |v(n)| < R,  ∀ i ∈ inputs, |hstep(hs(n − 1), i).v| < R,  ¬Follow(n)
    →   rs(n + 1) = 0
  （前は C + 34 ≤ n で、最後の前提は n ≠ C + 34 のときだけ）

ab_early（RoomRun のフィールド。狭めた）:
  C + 34 ≤ n,  n + 1 < C + 37,  n < t0,  ¬CleanR(n),  ¬AtCtrl(n − 1),  (¬Stale(n − 1)  ∨  AirNoSide(n − 1))   →   ab(n) < A
  （ラウンド 32 では、最後の 2 つの前提の代わりに  (n = C + 34  ∨  CleanW(n − 1)  ∨  ¬AtCtrl(n − 1))）

ab_run（RoomRun のフィールド。狭めた）:
  C + 37 ≤ n + 1,  n < C + 40,  rs(n) = 0,  ¬Follow(n),  st(n) = 0,  inp(n + 1).jump = false,  ab(n) ≠ |v(n)|,
  ¬AtCtrl(n − 1),  (¬Stale(n − 1)  ∨  AirNoSide(n − 1))   →   ab(n) < R
  （ラウンド 32 では、最後の 2 つの前提の代わりに  (CleanW(n − 1)  ∨  ¬AtCtrl(n − 1))）

NumFacts.amax_air（ROM のチェック）:   amax + 255 < 256 · A
```

`T(n − 1)` で `AtV` があるとき（部屋の歩きがくれる）、`¬AtCtrl(n − 1) ∧ ¬Stale(n − 1)` は、そこで押している向きが隠されていることです。それで 2 つのフィールドを求めるのは 2 種類のフレーム `n` だけです。保存された速さが `|v|` で押している向きが隠された状態でプレイヤーのルーチンに来るフレームと、空中で左も右も押さずに古い保存された速さで来るフレームです。新しいフィールドはどちらも前より少ないフレームで求めます: 新しい前提から古い前提が出ます。

## しくみ

**モデルに従うフレームの保存された速さ。** `FrameModel.stored_path`（ラウンド 13）は、プレイヤーのルーチンで当たりのビットが `TopSpeed.collBits` の値の 1 つであることを求めます。`ImposeFriction` の段を `TopSpeed.frictionCheck` と比べるからで、そのチェックはその値でルーチンを動かします。モデルに従うフレームがくれるのは `bits &&& lr = lr`（押している向きが隠されていない）だけです。部屋の歩きは、フレームの終わりでほかのビットを知りません（ラウンド 32）。`ImposeFriction` がビットを読むのは 1 回で、`lr` との `and` です。それで新しい `ImposeFriction` の歩き（`storedFricM`）は、ビットが `lr` の上だけで（1 と）わかっている本物の機械を、ビットが `0xFF` のモデルの機械と並べて動かします。`and` のあと、どちらも `lr` を持ちます。歩きは、2 つが同じ速さと保存された速さで終わることを示します。すると、ビット `0xFF` での `frictionCheck` が、動かす段で `xa = |v|` をくれます（`fric_absM`）。`stored_c4M`、`stored_pathM` がそれを `PlayerSubs` まで運びます。そこからは、`CleanW.after`（速さを書くものはない）と `InRoom.absAfter`（保存された速さを書くものはない）で `end_cleanW` になります。`InRoom.absKeep` と `InRoom.absBefore` が次のプレイヤーのルーチンまで運びます（`ab_cleanW`）。

**不変な性質。** `absOr0` は部屋のフレームについての帰納法です。最初の操作では、保存された速さは 0 で、速さも 0 です（`StartAt`）。モデルに従うフレームは `xa = |v|` で終わります（`end_cleanW`）。止めるフレームは、`PlayerSubs` に `xa = |v|` で来るか、空中で左も右も押していないときは、プレイヤーのルーチンでの速さと保存された速さで来ます。それは 1 つ前のフレームの終わりのものです（`stored_pathF`: 保存された速さに条件のない `stored_path`。そこでは `ImposeFriction` は動きません）。`PlayerSubs` のあと、当たりのルーチンは速さをそのままにするか 0 にし（`FrameModel.Collide`）、保存された速さを書くものはありません。どの場合も、フレームは `xa = |v|` か `v = 0` で終わります。

**古い保存された速さ。** フレーム `n + 1` が `xa ≠ |v|` でプレイヤーのルーチンに来るなら、`absOr0` から 1 つ前のフレームは `v = 0` で終わっています。それでフレーム `n + 1` は速さ 0 と端数で始まります。これは摩擦の下の限りつきの `TopSpeed.Frame` です（`FrameModel.frame_readQL`）。移動の終わりで `256·v₂ + f₂` は `−amax` から `255 + amax` の間なので、`256·|v₂| ≤ 255 + amax` です。`stored_pathF` から、そこでの保存された速さは `|v₂|` か、（空中で左も右も押していないとき）持ち越した古いものです。フレームが `PlayerSubs` に来るのは 1 回です（`InRoom.absAfter`）。加える量 1 つと端数は 1 フレームに 0.2 px より小さく、`A` より下なので（`NumFacts.amax_air`）、`|v₂| < A ≤ R` です。

**`C + 37` からの `stop_run`。** `RoomCore.stop_run` を使うのは `rs_of_safe3` だけで、それを呼ぶもの（`rs_of_safe`、`no_wall_back`）は壁にぶつかりません（`NoWall`）: `C + 37` より前のフレームはどれも `hstep` に従います。`rs_of_safe3` はいま `NoWall` を受け取り、`stop_run` を `hstep` に従わないフレームだけで使うので、`C + 37` からだけです。それで `stop_run_of` はもう `ab_early` を読みません。`ab_early` の `n = C + 34` の場合は、これと `ab_of` のためだけに求めていました。

**`ab_of` での `ab_early`。** `RoomCore.ab_of` は、`C + 34` から `C + 36` での止まりのあと、保存された速さが `A` より下か `|hstep(hs(n − 1), inp(n)).v|` であると言います。`ab_of_run` はいま、フレーム `n` で分けます。モデルに従う（`ab_cleanW` が 1 つ目の場合 `ab = |v|` をくれる）、`AtCtrl` の状態で止める（`ab_fresh` が `hstep` の場合をくれる。`C + 34` でも）、古い保存された速さで止める（`ab_stale` が `< A` をくれる。空中で左も右も押していないときは別）、またはフィールドです。

## 測ったこと

`room-ab-check FM2`（TAS と、最初の操作からの自分の入力の走り 2,800 回。このラウンドのプログラム）。ラウンド 32 のフィールド `ab_early` のフレーム（フレーム `n + 1` がモデルに従わない。`n` は `C + 34` か `C + 35`）を、フレーム `n` がしたことで分けたもの:

| フレーム `n` | `n = C + 34` | `n = C + 35` |
|---|---|---|
| モデルに従う（いまは `ab_cleanW`） | 117 | 77 |
| `AtCtrl` の状態で止める（`ab_fresh`。`C + 34` ではこのラウンドから） | 162 | 117 |
| 古い保存された速さで止める | 37 | 6 |
| そのうち空中で左も右も押していない（フィールド） | 37 | 6 |
| 向きが隠された状態で止める（フィールド） | 0 | 0 |
| ほか | 0 | 0 |

ラウンド 32 のフィールドはこのうち 316 + 83 = 399 フレームで求めていました。このラウンドのフィールドが求めるのは 43 です。古いものはどれも空中で左も右も押していなかったので、`ab_stale` の 1 つ目の場合が取ったものはありません。その保存された速さは 1 フレームに 0.375 px 以下です。TAS にはありません。入るまでの部屋のどのフレーム（336,111 フレーム）でも、終わりは `xa = |v|` か `v = 0` です（`absOr0`）。`C + 34` で `AtCtrl` の状態で止まったあとの `|hstep(hs(n − 1), inp(n)).v|` はいちばん大きくて 1 フレームに 0.4375 px で、`A` より下です。

`room-approach-check FM2 300 1` と `… 300 0`（フィールド `ab_run`）: ラウンド 32 のフィールドのフレームは 0 なので、新しいものも 0 です（カウンター 82、83）。`room-stored-check`: `storedM` はどの場合でも成り立ち（約 0.2 秒）、`amax + 255 < 256·A` です。

## 摩擦の両側を 1 回で

`TopSpeed.frictionCheck`（`ImposeFriction` のあとの速さを上から押さえ、保存された速さも見る）と `frictionLowCheck`（下から。ラウンド 30）は、同じ機械で `ImposeFriction` を動かしていました: すべての速さ、256 の端数、加える量、上限、4 つの入力、当たりのビット。`FrameModel.frictionBoth` はどの機械でも 1 回動かして両方を見ます。`friction_of_both` がそこから 2 つのチェックをくれます。非公開の `Proof/TopSpeedFriction.lean` はいま `fric_both` を `native_decide` で証明し、`top_frictionCheck` をそこから出します。`Proof/RoomFricLow.lean` は `room_fric_low` を探索なしでそこから取ります（約 100 秒かかっていました）。`frictionLowCheck` は `RoomJoin.lean` から `StoredClean.lean` に移りました。命題は同じです。指示にあるもう 1 つのやり方、ルーチンの道筋から 2 つの限りを証明することはしていません。

## 残ること（証明していない）

- 1 つ前のフレームが、保存された速さが `|v|` で押している向きが隠された状態でプレイヤーのルーチンに来るときの `ab_run` と `ab_early`。そこで `stored_path` は移動の終わりの保存された速さ `|v₂|` をくれますが、`v₂` は隠された向きでの摩擦のもので、`hstep` のものではありません。左と右を両方押して片方が隠されていると、`ImposeFriction` は速さをモデルと逆の向きに押すので、`|v₂|` はどのモデルの 1 歩よりも加える量 1 つ多くなりえます。測ったものはありません。
- 空中で左も右も押さずに古い保存された速さを持ち越したあとの同じ 2 つのフィールド。保存された速さは前の止まりの移動の終わりのもので、落下の中では定理はそれを押さえません。`ab_early` に残った測ったフレーム 43 はどれもこれです。

**ファイル。** 新しい `Theorems/StoredClean.lean`（`tagsFrM`、`storedFricM`、`storedM`、`fric_absM`、`stored_c4M`、`stored_pathM`、`stored_c4F`、`stored_pathF`）。`Theorems/RoomJoin.lean`: `Checks.storedM`、`NumFacts.amax_air`、`RoomRun.end_cleanW`、`ab_cleanW`、`absOr0`、`stale_arith`、`ab_stale`。フィールド `ab_early`、`ab_run` を狭めた。`RoomCore.stop_run` は `C + 37` から。`rs_of_safe3`、`rs_of_safe` は `NoWall` を受け取る。`ab_of_run`、`stop_run_of`。`StoredClean.lean` には `frictionLowCheck`（移した）、`frictionBoth`、`friction_of_both` も。プログラム: `room-stored-check`（新しい）、`room-ab-check`（上の分け方）、`room-approach-check`（カウンター 82、83）。非公開: `Proof/TopSpeedFriction.lean`（`fric_both`）と `Proof/RoomFricLow.lean`。どちらも `genRoomFricLow` が書きます。
