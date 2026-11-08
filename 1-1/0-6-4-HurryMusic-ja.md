[← Back](README-ja.md) | [English](0-6-4-HurryMusic.md) | [Japanese](0-6-4-HurryMusic-ja.md)

# 急ぎの音楽が鳴る走り

**命題.** 急ぎの音楽が鳴る走りでは、1-2 は 1748 フレームより前に始まりません。城に入るフレームを `E` とすると `q · (t0 − u) ≤ E + 3q` です。ゲームの値 `q = 24`、`t0 = 401`、`u = 100` では `E ≥ 7152` です。

**これは仮定つきの定理です。** 仮定は `HurryMusic.Run` のフィールドです。下に全部挙げます。

ゲームはタイマーが 100 を示すフレームで急ぎの音楽をキューに入れます。この音楽が鳴る走りは、横の土管で `chg.entry₂` を満たしません（音楽のバイトと `NoteLengthTblAdder` が違います）。なので [1-1 全体](0-1-Route-ja.md) の `Run` に入りません。この定理はその走りを別に扱います。

## 定理

`seq n` はフレーム `n` が始まるときの機械です。`s(n)` はフレーム `n` が始まるときの `clock` のカウンタです（`CastleToLevel.Frames`。`Route.Run.clock` と同じものです）。`timer(m)` は機械 `m` のタイマーの 3 桁の値です。

`hurryOn(m)` は、機械 `m` で急ぎの音楽がキューにあるか、鳴っているか、そのあとの曲を速くしていることです。

```
hurryOn(m)  =  EventMusicQueue(m) = TimeRunningOutMusic  ∨  EventMusicBuffer(m) = TimeRunningOutMusic  ∨  NoteLengthTblAdder(m) ≠ 0
```

`HurryMusic.Run` のフィールドです。

```
clock, order   Frames（各フレームは Step と plan に従う）と、区間の順序
next           seq(n + 1) = frame(seq n, inp n)
title          タイトルで Start を押してからフレーム 0 まで（TitleStart.Begin）
read₀          s(0).t = timer(seq 0)
k, hk, on      k ≤ E + 1,  hurryOn(seq k) = true
music          n < k,  hurryOn(seq n) = false,  hurryOn(frame(seq n, inp n)) = true  ⟹  timer(seq n) ≤ u        （1 フレーム）
below          n < k  ⟹  s(n).t ≤ timer(seq n)
L, after       E < L
```

定理です。

```
Frames.late         :  s(0).t = t0,  n ≤ E + 1,  s(n).t ≤ u  ⟹  q · (t0 − u) ≤ E + 3q
Run.zero            :  timer(seq 0) = t0                （title と確かめ title_check から）
Run.quiet₀          :  hurryOn(seq 0) = false           （title と確かめ title_check から）
Run.late            :  1 ≤ q  ⟹  q · (t0 − u) ≤ E + 3q
Run.level_ge        :  1 ≤ q,  1748 + 3q ≤ q · (t0 − u)  ⟹  1748 ≤ L
hurry_1_1（非公開）  :  q = 24,  t0 = 401,  u = 100  ⟹  1748 ≤ L
```

`q · (t0 − u) = 24 · 301 = 7224`、`1748 + 3q = 1820` です。`k` は城に入るまでのどのフレームでもかまいません。`chg.entry₂` を満たさない走りでは、横の土管の入口のフレームです。

証明です。

* `hurryOn` はフレーム 0 で偽、フレーム `k` で真です。なので偽から真になるフレーム `n < k` があります（`first_on`）。`music` から `timer(seq n) ≤ u`、`below` から `s(n).t ≤ u` です。
* `Frames.late`: どのフレームもタイマーの数字を上げません（`t_anti`）。なので `T = s(E + 1).t ≤ u` です。`hT` から `t0 − u ≤ ⌈p₁/q⌉ + ⌈p₂/q⌉ + ⌈p₃/q⌉` です。`p₁`、`p₂`、`p₃` は 3 つのエリアのプレイのフレーム数です。`q · ⌈p/q⌉ ≤ p + q − 1` で、`p₁ + p₂ + p₃ ≤ E` です。
* `Run.level_ge`: `L > E ≥ q · (t0 − u) − 3q ≥ 1748` です。

`hT` はどのサブカウンタから始めても成り立ちます（`playN_drop`）。プレイ `p` フレームで、タイマーの数字は `⌈p/q⌉` より多くは減りません。なので音楽の 1 フレームとタイマーの規則だけで足ります。

## 本物のフレームでの確認

`hurry-check FM2` です。終了コード 0 です。

```
動画、フレーム 0 が始まるとき             timer 401,  位相 2,  hurryOn false
動画、1760 フレーム                       音楽が始まるフレーム 0、Step に合わないフレーム（城まで）0
タイマーを書き換えた走り                  動画の 12 のフレーム（100 から 1100）で数字を 100、101、102、103、105、110、124 に書き換え、
                                          そこから動画の入力、または乱数の入力とポーズで 600 フレーム。168 回、100,800 フレーム
  音楽が始まるフレーム                    108。始まりのタイマーは全部 100。u = 100 を超えるものは 0
  Step に合わないフレーム（城まで）       動画の入力 0。乱数の入力 11。全部ルーチン 0 と 7、死んで面をやり直すフレーム
  横の土管の入口（フレーム 571）で音楽    23 回
```

音楽が始まらなかった 60 回は、タイマーが動かない切り替えか、触ったあとか、600 フレームでは 100 まで下がらない値です。

## 証明していないこと

* `music` は 1 フレームの仮定です。コードでは、急ぎの音楽をキューに入れるのは `RunGameTimer` だけで、タイマーが 100 のときです。`EventMusicBuffer` はキューから写します。`NoteLengthTblAdder` を 0 でない値にするのは、キューの急ぎの音楽を読み込むときだけです。これはコードから読んだもので、上の 108 フレームで確かめました。
* `below` と `read₀` はカウンタと機械のつながりです。はみ出すフレームのない走りでは、`clock` のカウンタは機械から読んだ値なので、等号で成り立ちます。はみ出すフレームでは、境目の数字はルーチンが残す数字より小さくありません。ルーチンは数字を下げるだけだからです。これはコードから読んだもので、確かめていません。
* `title` は [タイトルの Start から操作できるまで](0-5-3-TitleStart-ja.md) の仮定です。押したあとの機械の 1 つの条件と、操作できるまでのゲームコアのフレームで Start を押さないことです。`zero` と `quiet₀` はもうフィールドではありません。ここから証明します（`Run.zero`、`Run.quiet₀`）。
* `clock` の `step` と `plan` は `Route.Run` と同じ仮定です（[1-1 全体](0-1-Route-ja.md)）。パワーアップのある走りと死ぬ走りは `plan` に従わないので、ここにも入りません。

**ファイル.** `Theorems/HurryMusic.lean`、`Theorems/CastleToLevel.lean`（`Frames.late`、`playN_drop`）、`Theorems/TitleStart.lean`、非公開の `Proof/HurryMusic.lean` と `Proof/TitleStart.lean`。

**再現.**
```
.lake/build/bin/smbrta hurry-check FM2
```
