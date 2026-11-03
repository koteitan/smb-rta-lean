[← Back](../README-ja.md) | [English](emulator.md) | [Japanese](emulator-ja.md)

# エミュレータ

ファミコンを Lean で書き、その上でゲーム自身のコードを動かします。

* `Smbrta/Cpu.lean` — 6502（2A03）。公式の命令全部と、安定して動く非公式の命令。ページをまたぐ
  ときと分岐のときの追加サイクルも含めて、サイクル数まで正確です。
* `Smbrta/Machine.lean` — 2 KiB の RAM、NROM のカセット、コントローラ、OAM DMA の待ち時間、
  そして PPU はタイミングだけ（vblank の合図、NMI、スプライト 0 ヒット）。絵は描きません。
  ゲームの処理は絵に依存しないからです。RAM の読み書きの記録（書く前に読んだバイト、書いたバイト）
  を取ることもでき、フレームが何を引き継ぐかを見つけるのに使います。
* `Smbrta/Movie.lean` — FCEUX の `.fm2` 形式の TAS。フレームは vblank から vblank まで。

**確認.**

| 確認 | 結果 |
|---|---|
| nestest のログ（レジスタ、フラグ、サイクル数） | 8991 行すべて一致 |
| 自作のテスト ROM（フレーム、NMI、コントローラ）。`native_decide` の定理としても | 一致 |
| 2 本の TAS を電源 ON から（`smbrta run`） | どちらも 8-4 の斧に届く |
| 別に作った、本物の PPU を持つエミュレータ | 面の切り替わりもクリアのフレームも同じ |

**信じている部分.** `native_decide` は Lean のコンパイラが正しいことを信じます（`Lean.ofReduceBool`）。
