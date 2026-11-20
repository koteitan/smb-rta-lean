[← Back](README-ja.md) | [English](c-7-1-4-RoomLag.md) | [Japanese](c-7-1-4-RoomLag-ja.md)

# 部屋で一時停止する走り

**主張.** 部屋のフレームは、いまは部屋で最初に操作できるフレーム `b₁` からの走りのフレームのうち、ゲームが止まっていない状態で終わるものです。止まった状態で終わるフレームはプレイヤーのルーチンに来ず、部屋のモデルが読むバイトをすべて保ちます。なので、かたまりを越える前に部屋で一時停止する走りも定理に入ります。フィールド `unpaused` はなくなりました。新しいフィールドは `roomLag` です: 部屋で止まった状態で終わるフレームは `clock` の `lag` のフレーム。

このラウンドの前、`RoomRun` は部屋のフレーム `n` が走りのフレーム `b₁ + (n − C)` で終わるとしていました。なので部屋のすべてのフレームがモデルのフレームでした。フィールド `unpaused` は、`t₀` までの各フレームが止まっていない状態で終わることを求めていました（[部屋のフレーム: プレイヤーのルーチンでの状態](c-7-1-2-RoomCut-ja.md)）。部屋で一時停止する走りはこれを満たしません。パート a と f はすでに、止まっていない状態で終わるフレームだけを数えています（`PipeFrames.Lags`、`FrameKeep.Keep`）。いま部屋も同じにしました。

## 部屋のフレーム

`S` は走り（`Route.Run.base`）、`seq(k)` はフレーム `k` が始まるときの機械、`pz` は一時停止のバイト、`R` はプレイヤーのルーチンです。`lim = a₂ − b₁` で、`a₂` は `b₁` から後で最初にプレイヤーのルーチンを離れた機械です（`Route.Base.a₂`）。

```
up(k)     :  pz(seq(b₁ + k)) & 1 = 0                  フレーム b₁ + k − 1 は止まっていない状態で終わる
ups       :  #{ k : 1 ≤ k ≤ lim,  up(k) }
ix(j)     :  up(k) となる j 番目の k ≥ 1。ix(0) = 0     （FrameKeep.ixOf。パート f と同じ）
fe(n)     :  seq(b₁ + ix(n − C))                      部屋のフレーム n の終わり
fm(n)     :  seq(b₁ + ix(n + 1 − C) − 1)              部屋のフレーム n + 1 が始まるところ
```

これらは定義です（`RoomJoin.ixR`、`endAt`、`startAt`、`inpAt`。`RoomRun.fe`、`RoomRun.fm`）。`RoomRun` は新しいパラメータ `lim` をとります。モデルは各フレームの終わりで横の状態、位置、縦の状態を読みます（`read_hs`、`read_P`、`read_vs` は `fe(n)` で）。1 フレームの条件（`clean`、`read_in`、`read_ab`、`ab_early`、`farNear`、`enters`、`read_PE`。以前は `vfloor` も）は `fm(n)` からの本物のフレームについてです。

```
RoomRun.next     :  C ≤ n,  n + 1 − C ≤ ups  →  fe(n + 1) = frame(fm(n), inAt(n))
RoomRun.up       :  C ≤ n,  n + 1 − C ≤ ups  →  pz(frame(fm(n), inAt(n))) & 1 = 0
RoomRun.between  :  ix(n − C) ≤ k,  k + 1 < ix(n + 1 − C)  →  pz(seq(b₁ + k + 1)) & 1 = 1
RoomRun.fe_C     :  fe(C) = seq(b₁)
RoomRun.arrive   :  C ≤ n < t₀  →  pc(tr_n(arr(n))) = R                    （前はフィールド unpaused から）
```

`tr_n(j)` は `fm(n)` からのフレームの `j` 命令目の機械です。

## 止まった状態で終わるフレーム

[RoomVert](c-7-5-1-RoomVert-ja.md) のプレイヤーのルーチンへの歩きは、フレームが `R` に来たことを表すビットを持ちます。いまはフレームの終わりでもっと求めます（`finA`）: `R` に来た状態は一時停止のバイトの下位ビットが 0 と知っていて、来ていない状態は 1 と知っている。検査 `RoomVert.checkA` は今も成り立ちます。表は同じ（69,913 状態）、時間も同じ（プログラムで 6.4 秒）です。これから:

```
end_R     :  RoomCond(M),  各命令で SiteOK  →
               (∃ j,  pc(tr(j)) = R)  →  pz(end) & 1 = 0
               (∀ j,  pc(tr(j)) ≠ R)  →  pz(end) & 1 = 1  ∧  ∀ x ∈ vKeepA,  end[x] = M[x]
paused_R  :  RoomCond(M),  SiteOK,  pz(end) & 1 = 1  →  ∀ x ∈ vKeepA,  end[x] = M[x]
```

`vKeepA` には `readHS`、位置、`vsOf` のバイトが入っています（`RoomVert.model_eq_of`）。なので、部屋のフレーム `n` の終わりからフレーム `n + 1` の始まりまでのフレームは、モデルが読むものを保ちます（`Run.roomKeep`。`InRoom` の新しい部分 `keep`）:

```
Run.roomKeep  :  C ≤ n < E  →  readHS(fm(n)) = readHS(fe(n))  ∧  P(fm(n)) = P(fe(n))  ∧  vs(fm(n)) = vs(fe(n))
```

これらのフレームはどれも部屋の中の `base` のフレームなので、部屋の条件で始まり（`RoomMap.cond_of_rows`）、`SiteOK` を満たします（`chg.roomSites`）。

## 数えることに要るもの

`room.C` と `room.E` は `clock` が決めます: `chg.hb₁` は `seen(b₁) = C + 1`、`chg.ha₂` は `seen(a₂) = E + 1` と言います。`seen(k)` は `k` より前の `lag` でないフレームの数です。部屋のフレームは止まっていない状態で終わるフレームです。証明には、部屋のフレーム `E` が `a₂` までに見つかることが要ります:

```
Run.roomMany  :  E − C ≤ ups
```

これは各フレームの 1 つの条件、新しいフィールド `roomLag` から出ます:

```
roomLag  :  b₁ ≤ n < a₂,  pz(seq(n + 1)) & 1 = 1  →  kind(n) = lag
```

すると `E − C = #{ n ∈ [b₁, a₂) : kind(n) ≠ lag } ≤ #{ n ∈ [b₁, a₂) : pz(seq(n + 1)) & 1 = 0 } = ups` です。`E − C ≤ ups` から、入る前の部屋の各フレームは部屋の中の `base` のフレームで始まります（`Run.roomIdx`: `b₁ ≤ b₁ + ix(n + 1 − C) − 1 < a₂`）。歩きの定理もそうです（`roomBump`、`roomArrive`、`roomBefore`、`roomReach`、`roomCut`、`roomTime`、`roomVert`、`roomPair`、`roomEnter`）。

要るのは片方の向きだけです。もし止まっていない状態で終わるフレームが `lag` のフレームなら `E − C < ups` です。すると部屋のフレーム `E` は本物の入るフレームより前に来て、その走りで `enters` は成り立ちません。下の本物の走りにそういうフレームはありません。`roomLag` は「`lag` のフレームは止まった状態で終わるフレーム」という規則の部屋の部分です。地上では `Run.LagUp`、最初の切り替えでは `chg.paused₁` がそれにあたります。

## なくしたもの、加えたもの

* なくした: フィールド `room.unpaused`。
* 加えた: `Route.Run` のフィールド `roomLag`。`RoomRun` のパラメータ `lim`。`InRoom` の部分 `many` と `keep`（定理 `Run.roomMany`、`Run.roomKeep`）。
* 変えた: `RoomRun` のフレーム（上の定義）。`RoomJoin.StartAt` は `fe(C)` で求め、`Run.roomCtl` は `fe(C) = seq(b₁)` と言います。`InRoom.vert` と `farNear` の結論は `frame(fm(n), inAt(n))` で。`RoomVert.finA` は来たあとのビット 0 を求めます。

## 本物のフレームで確かめた

`room-lag-check FM2`（約 32 秒）: 部屋に一時停止を入れたムービー（フレーム `f` で Start、何も押さない、`f + d` で Start、そのあとムービーの入力を `d` フレーム遅れで）。`f` は 461 から 569 まで 6 ずつ、`d` は 45、50、77。それと、部屋で最初に操作できるところからの自分の入力 40 回、300 フレームまで、8 フレームに 1 回 Start。`d` = 44 だと 2 回目の Start は一時停止のタイマーがまだ動いているときに来て、ゲームは止まったままです。

| | |
|---|---|
| 一時停止を入れて横の土管に着いた走り | 57 回のうち 57 |
| 止まった状態で終わる部屋のフレーム | 3,268 |
| そのうち位相が動くもの（`roomLag` に反する） | 0 |
| そのうちプレイヤーのルーチンに来るもの | 0 |
| そのうち `vKeepA` のバイトを変えるもの | 0 |
| 位相が止まっていて、止まっていない状態で終わる部屋のフレーム | 0 |
| `roomMany` に反する走り | 0 |
| 数えるフレーム `E − C` が入るフレームでない走り | 0 |
| `vKeepA` が一時停止のないムービーのフレームと違う数えるフレーム | 0 |
| 自分の入力: フレーム、止まって終わる、位相が動く、`vKeepA` を変える | 12,000、6,248、0、0 |

フレーム 500 で 60 フレーム一時停止した走りでは、前の定義は入るフレームを `base` のフレーム 570 にしていました。でも本物の入るフレームは 630 です。前の `enters` と `unpaused` はそこで成り立っていませんでした。

## 証明していないもの

* `roomLag`（各 1 フレーム、新しい）: 部屋で止まった状態で終わるフレームは `lag` のフレーム。部屋の中で `clock` の種類を機械に結びます。
* `RoomRun` のほかのフィールド。前と同じです。いまは数えるフレームだけに求めます。

**ファイル.** `Theorems/RoomJoin.lean`、`Theorems/RoomVert.lean`、`Theorems/Route.lean`、`Main.lean`（`room-lag-check`）。

**再現.**
```
.lake/build/bin/smbrta room-lag-check FM2       # 部屋での一時停止: roomLag、数、止まって終わるフレーム
.lake/build/bin/smbrta room-ctrl-check FM2 [N]  # 新しい finA の checkA
```
