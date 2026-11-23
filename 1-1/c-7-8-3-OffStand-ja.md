[← Back](README-ja.md) | [English](c-7-8-3-OffStand.md) | [Japanese](c-7-8-3-OffStand-ja.md)

# かたまりの上の立ち: 落ちるときに読まないバイト

ラウンド 34 で、[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `offStand` が `Off` の一部の代わりになりました（[かたまりの上から: 床までのフレーム](c-7-8-2-OffDrop-ja.md)、項目 1-1-c-7-8-2）。それは次を言っていました。フレーム `t0 − 1` が立って終わるなら、ジャンプの力は落ちる力に等しく、落ちる力は踏み切りのもの（`forces`）の 1 つで、ジャンプの起点はかたまりの上か `N.heights` の高さです。証明はそれを、その立ちをチェック `standB` のリスト `standFam` に入れるためだけに使いました。ラウンド 35 で `offStand` はなくなりました。代わりに次の 2 つの事実があり、どちらも証明しています。

* 入る前の部屋のどのフレームも、部屋の落ちる力で終わる。
* 立つときと落ちるときは、ジャンプの力もジャンプの起点も読まない。それでこの 2 つのバイトを知る必要はない。

## 証明したこと

`vstepR(s, a)` は、垂直の状態 `s` から A ありかなしで、ゲームの動きのルーチン（`PlayerMovementSubs`）を 1 フレーム、プレイヤーのルーチンの機械で走らせたものです（`RoomJoin.vstepR`）。`vE(n)` は部屋のフレーム `n` の終わりの垂直の状態で、機械から読みます。`s[vf := v, origin := o]` は、ジャンプの力を `v`、ジャンプの起点を `o` にした `s` です。

```
OffStand.air_keep  :  st(s) ∈ {1, 2}  →  vfd(vstepR(s, a)) = vfd(s)  ∧  origin(vstepR(s, a)) = origin(s)  ∧  st(vstepR(s, a)) = st(s)
OffStand.fall_same :  st(s) = 2  →  vstepR(s, a) = vstepR(s[vf := v, origin := o], a)[origin := origin(s)]
RoomRun.vfd_ok     :  ∀ n ∈ [C, E),  vfd(vE(n)) ∈ forcesR
RoomRun.off_stand  :  st(vE(t0 − 1)) = 0  ∧  y(vE(t0 − 1)) = y_top  →  t0 + aboveF ≤ E + 1
```

`forcesR`（`RoomJoin.forcesR`）は、踏み切りの落ちる力（`forces`）と、最初の操作の状態（`N.vStart`）の落ちる力です。

**空中の動きのルーチン**（`air_keep`、`fall_same`）。空中（状態 1 か 2）では、ルーチンは落ちる力も、ジャンプの起点も、状態も書きません。書くのは踏み切りだけで、泳ぎのフラグが 0 の空中ではルーチンは踏み切りません。落ちるとき（状態 2）は、まず落ちる力をジャンプの力に写し、ジャンプの起点は一度も読みません。それで、ジャンプの力と起点だけが違う 2 つの落ちる状態は、起点のほかは同じ次の状態になります。起点はそれぞれ自分のものを保ちます。証明は `runSub` の 2 つの機械の歩き（`FrameModel.runSub2`）で、水平の部分には垂直のモデルの回り道（`VertModel.detours`）を使います。チェック `OffStand.keepOK` は 8 つの歩きです。状態 1 か 2、A ありかなし、前のフレームの A ありかなしです。

**落ちる力**（`vfd_ok`）。最初の操作で、落ちる力は `N.vStart` のどれかのものです（`InRoom.vstart`）。立って始まりジャンプのないフレームはそれを保ちます（`StandNext`）。段からの踏み切りは `forces` の 1 つを持ちます（16 の段の踏み切りでのチェック `offVfdCheck`。立ちは `stand_ok` で段の上です）。空中ではルーチンがそれを保ち（`air_keep`）、着地も保ちます。

**立つときと落ちるときに読まないところだけが違う 2 つの状態**（`SimV`）。`SimV(a, b)` は、`a` と `b` の高さ、端数、垂直の速さ、落ちる力、状態、前のフレームの A が同じで、状態が 0 でも 2 でもなければジャンプの力と起点も同じ、ということです。

```
offNext_sim :  SimV(a, b)  ∧  t ∈ offNext(a)  →  ∃ t' ∈ offNext(b),  SimV(t, t')
nearB_sim   :  SimV(a, b)  →  near(a) = near(b)
```

立ちはその 2 つのバイトを保ち（`StandNext`）、踏み切りは両方を書きます。それで `SimV` の 2 つの立ちの次の状態は、また `SimV` です。2 つの落ちる状態では `fall_same` です。それで、かたまりの右端を越えたあとの本物のフレームの道で、あるリストの状態 `w` と `SimV` の状態から始まるものは、`w` からの `offNext` の道が一歩ずつ追います（`offB_path_sim`、`offB_gap_sim`）。

**`t0 − 1` の立ち**（`off_stand`）。フィールド `offTop` がその立ちをかたまりの上に置きます。`stand_ok` でそれには垂直の速さがなく、`vfd_ok` で落ちる力は `forcesR` のものです。それで、`vE(t0 − 1)` のジャンプの力をその落ちる力に、起点をかたまりの上にした状態 `w` は `standFam` にあり、`SimV(vE(t0 − 1), w)` です。`w` からチェック `standB` は、`aboveF − 1 = 12` フレームのあいだ床の近くの状態を見つけません。それで入るのは `t0 − 1` から 12 フレームより先で、前と同じです。

## フィールド

なくなったもの:

* `offStand`（`RoomRun` のフィールド）。

加えたもの: フィールドはありません。`RoomJoin.Checks` の新しい ROM のチェック（非公開の `Proof/RoomJoin.lean` で `native_decide`）: `keepA`（`OffStand.keepOK`）と `offVfd`（`offVfdCheck`）。チェック `standB` は小さくなった `standFam` から始めます。`forcesR` の落ちる力、起点はかたまりの上だけ、どの端数も、A ありかなしで、2,048 の状態です（前は 6,144: `forces` の落ちる力、かたまりの上と `N.heights` の起点）。ラウンド 35 からは、どの高さへの着地も許し、どの状態も 1 回だけ追います（[かたまりの右端を越えたあと: どの高さへの着地も](c-7-8-4-OffLand-ja.md)）。

チェック `offVfdCheck` は最初の形では成り立ちませんでした。それは最初の操作の落ちる力が `forces`（踏み切りの 3 つの落ちる力）の 1 つであることを求めました。実際はそうでなく、部屋の始まりの機械の落ちる力で、3 つのどれよりも小さい力です。最初の踏み切りまでそのままです。それで不変な性質は `N.vStart` の落ちる力も許し、`standFam` は 4 つ目の落ちる力としてその力を持ちます。古いフィールド `offStand` は測った走りでは偽ではありませんでした（ラウンド 34 で反するもの 0）。そこでは、かたまりの上に立つ前に彼は踏み切っていました。

## 測ったこと

`room-off-stand`（このページのチェックを ROM で）:

| チェック | 結果 | 時間（ネイティブ） |
|---|---|---|
| `keepOK`（空中の動きのルーチンの 8 つの歩き） | 真 | 55 ms |
| `offVfdCheck`（16 の段の踏み切りと最初の操作の状態の落ちる力が `forcesR` の 4 つの値のもの） | 真 | 1.2 秒 |
| `standB`（`standFam` の 2,048 の立ちから、`offNext` の 12 フレームのあいだ床の近くの状態がない） | 真 | 7.9 秒（ラウンド 34: 6,144 の状態で 14.5 秒） |

このフィールドに反する測ったフレームはありませんでした（ラウンド 34: `room-off-ways`、`t0 − 1` の立ち 34）。`room-off-ways` は今も数えます。

## 残ること（証明していない）

* `offTop`、`offSlow`（[かたまりの上から: 床までのフレーム](c-7-8-2-OffDrop-ja.md) にそれぞれの証明の道があります）。`offNear` はラウンド 36 で証明しました（[入るフレーム](c-7-8-5-EntryVert-ja.md)）。`offFloor` もラウンド 35 でなくなりました（項目 1-1-c-7-8-4）。

**ファイル。** `Theorems/OffStand.lean`（`keepOK`、`run_K`、`air_keep`、`fall_same`）。`Theorems/RoomJoin.lean`（`forcesR`、`standFam`、`offVfdCheck`、`jump_vfd`、`SimV`、`fall_sim`、`offNext_sim`、`nearB_sim`、`RoomRun.st_012`、`RoomRun.vfd_ok`、`RoomRun.offB_path_sim`、`RoomRun.offB_gap_sim`、`RoomRun.off_stand`。チェック `keepA`、`offVfd`）。`Main.lean`: `room-off-stand`。非公開の `Proof/RoomJoin.lean` に `keepA` と `offVfd` が入ります。

**再現。**
```
.lake/build/bin/smbrta room-off-stand     # このページと 1-1-c-7-8-4 のチェック（約 2 分）
```
