[← Back](README-ja.md) | [English](e-2-10-3-16-MoveScroll.md) | [Japanese](e-2-10-3-16-MoveScroll-ja.md)

# 動きがスクロールのために書くバイト

**主張（第 28 回）.** 地上の数えるフレームのスクロールの処理で、彼のピクセルは、フレームがプレイヤーのルーチンに最初に来たところのピクセルに、動きが書くバイトを足したものです。ただしそのバイトが 1 から 128 のとき。だから、スクロールの処理でのフィールド `near`（第 26 回と第 27 回）は定理 `OnFrames.nearAt` になります。もとになるのは、ルーチンに来たところの状態についての新しいフィールド `nearA` です。`nearA` は動きのことを言いません。1 つの場合では `near` より多くを求めます: 動きが書くバイトが 1 から 128 でないフレーム（スクロールの処理で右に動かないフレーム）では、`near` は何も求めませんでしたが、`nearA` はルーチンに来たところで 2 px の上限をなお求めます。測ったすべてのフレームで成り立ちました。

```
R = trace(fm j, pad j, arrAt)      プレイヤーのルーチンに最初に来たところ
Q = trace(fm j, pad j, k)          そのあとの最初のスクロールの処理
xs(Q) = 動きが書くバイト（スクロールの処理の最初の読み込みのオペランド）

move_xs :    1 ≤ xs(Q) ≤ 128  →  pixel16(Q) = pixel16(R) + xs(Q)

NearA(R) :=  side(R) = 0  →  lock(R) = 0  →  thr ≤ pfs(R)  →  left16(R) + 2 ≤ pixel16(R)
NearX(Q) :=  Allows(Q)  →  left16(Q) + xs(Q) + 2 ≤ pixel16(Q)            （前のフィールド near、第 27 回）

nearX_of_a :  NearA(R) ∧ (∀ x ∈ placeI, ram(Q)[x] = ram(R)[x]) ∧ plat(Q) = 0 ∧ move_xs  →  NearX(Q)

side = 横の当たりのタイマー、lock = スクロールのロック、pfs = 画面での彼の場所、thr = スクロールの 1 つ目のしきい値（80 px）、
pixel16 = 256·ページ + ピクセル、left16 = 画面の左端（ページつき）、plat = スクロールへの足場の力
```

`nearX_of_a` の証明: Allows(Q) は side(Q) = 0、lock(Q) = 0、thr ≤ pfs(Q)、1 ≤ xs(Q) + plat(Q) ≤ 128 を求めます。`PlaceKeep.keep_place` の歩きから、R でも同じ 3 つのバイトと同じ端です。だから NearA(R) から left16(Q) = left16(R) ≤ pixel16(R) − 2 = pixel16(Q) − xs(Q) − 2。

**動きのルーチン.** 動きのルーチンは `16·v` を 3 つの桁で位置に足します: 端数に下の桁 `l`、ピクセルに真ん中の桁 `d` と繰り上がり `c`、ページに上の桁と繰り上がり。ルーチンは `d + c` を返し、呼んだルーチンがそれをバイトとして書きます。確認 `MoveScroll.xsTailOK` は、動きのルーチンの各切れ目（`FrameModel.tailOK`）から 2 つの部分を歩きます:

1. 端数の読み込みから、すべての端数 `f` とすべての下の桁 `l` について: `f + l` の繰り上がりがスタックに積まれ、真ん中の桁、速さ、切れ目のバイトは書かれない;
2. ピクセルの読み込みから、すべての速さ `v` と繰り上がり `c` について: フレームはバイト `d + c` でスクロールの処理に来る。

`xsDigits` は 256 のすべての速さについて、`16·sbyte(v) = 256·sbyte(d) + l` で −8 ≤ sbyte(d) ≤ 7 であること、`d + c` が 1 から 128 のときは `sbyte(d) + c` であることを確かめます。`FrameModel.tail_spec` の位置の変わり方（`P(Q) ≡ P(R) + 16·v mod 2²⁴`）と合わせると、端数から繰り上がりが分かり、pixel16(Q) ≡ pixel16(R) + d + c (mod 2¹⁶) です（`pix_of_xs`）。位置はその範囲の端から離れているので（`Far`）、一周はしません。

**ルートの上で.** `OnFrames.nearAt` は、フレームがスクロールの処理まで読めること（`OnFrames.readH`）を使うので、前のフレームの速さと位置をとります。`OnFrames.edgeAt` と `OnFrames.edge_behind` もそれらをとります。呼ぶ側は `OnFrames.readAll` からそれらを持っています。フレームはスクロールの処理に 1 回だけ来ます（`GuardE.subs_onceE`）。`numbersCheck` には確認が 2 つ増えました: `PlaceKeep.placeCheck` と `MoveScroll.xsCheck`。

**測ったこと**（`surface-frames-check` と `edge-real` は、走るすべてのフレームで、ルーチンに来たところの `nearA` とスクロールの処理での `move_xs` を確かめます）:

| 確認 | 何を | 結果 |
|---|---|---|
| `xsCheck` のネイティブの試し | バイトの歩き、桁 | true |
| `edge-real FM2 256` | `nearA`、`move_xs` | 137,955 フレーム（clean でもそうでなくても）、失敗 0。スクロールが許される到着 11,289。場所のバイトがしきい値以上で横のタイマーが 0 の、ルーチンに来たところでの pixel − left の最小は 80 |
| `surface-frames-check FM2 200` | `nearA`、`move_xs` | 8 つの集まり、239,510 フレーム、clean で確かめた 215,433 フレーム、失敗 0。階段のあたりの書き換えた 103,680 の状態（第 27 回の `PlaceAt` が偽だったところ）のうち clean な 97,772 を確かめて失敗 0（ほかの 5,908 のフレームの始まりは clean でなく、`near` のときと同じく確かめていない） |
| `surface-frames-check FM2 200` | 次の回のために: フレームの始め `a` での `NearM(a)` := side(a) ≤ 1 → lock(a) = 0 → thr ≤ pfs(a) → left16(a) + 2 ≤ pixel16(a) | 8 つの集まりのすべてで、反するフレームの始めは 0。正確な形「side(a) ≤ 1 なら pfs(a) = pixel − left で 0 ≤ pixel − left < 256」は、書き換えた集まりの 50,760 のフレームの始めで偽、ほかの 7 つでは 0 |

**証明していないこと.** `nearA`。それには前のフレームが要ります: そこでの描画が画面での彼の場所を (pixel − left) mod 256 として書き、補正が彼を画面に保ち、押し戻しが横のタイマーを 16 にします。このフレームのタイマーの部分も要ります。そこは添字での書き込みで横のタイマーを減らします。

**ファイル:** `Theorems/MoveScroll.lean`（`lows`、`xsDigits`、`xsTailOK`、`xsCheck`、`xs_tail`、`pix_of_xs`、`move_xs`、`NearA`、`nearX_of_a`）。`Theorems/SurfaceFrames.lean`（`OnFrames.nearAt`）が使います。
