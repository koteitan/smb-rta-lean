[← Back](../README-ja.md) | [English](setup.md) | [Japanese](setup-ja.md)

# 準備

設定ファイルを書き、ROM を置いて、`prove.py` を実行してください。あとは全部 `prove.py` が行い、
最後に Lean が確かめた定理の一覧を表示します。コマンドは、このリポジトリのフォルダの中で実行して
ください。

## 1. 設定ファイルを書く

見本を `smbrta.json` という名前で、リポジトリの外の、このリポジトリのフォルダより上のどこかに
コピーして（今いるフォルダから上へ探します）、パスを書き換えてください。相対パスは、`smbrta.json`
のあるフォルダから数えます。

```bash
cp smbrta-tmpl.json ../smbrta.json
```

| キー | 何か | |
|---|---|---|
| `rom` | スーパーマリオブラザーズ（JU）の ROM（iNES 形式、マッパー 0） | 自分で置く（2 章） |
| `disasm` | 解析済みコード `SMBDIS.ASM` | 無ければダウンロードされる |
| `proofProject` | 作った証明を置く非公開の Lean プロジェクト（証明には ROM が入る） | 作られる |
| `syms` | 名前と値の表 | 作られる |
| `nestestRom`、`nestestLog`、`miniRom` | テストデータ | 作られる |

上へ探す代わりに、`--config FILE` で渡すか、環境変数 `$SMBRTA_CONFIG` に書くこともできます。

## 2. ROM を置く

手元のスーパーマリオブラザーズ（JU）の ROM を、`rom` に書いた場所にコピーしてください。ROM は
このリポジトリには入っていません。

```bash
cp /path/to/your/smb.nes rom に書いたパス
```

## 3. prove.py を実行する

```bash
python3 prove.py
```

失敗した段階があれば、そこでメッセージを出して止まります。証明は約 2 分です。
`python3 prove.py --full` では、全探索の証明も行います（さらに約 20 分）。
ビルドには `lake build` を使います。ほかのコマンドを使うときは、環境変数 `SMBRTA_BUILD` に書いてください。

## prove.py がすること

1. `tools/setup.py`:
   * ROM を確かめる（ヘッダーを除いた PRG + CHR の MD5 が `8e3630186e35d477231bf8fd50e54cdd`）。
   * 解析済みコードが無ければダウンロードし、SHA-256 を確かめる。
   * `proofProject` に非公開の Lean プロジェクトを作る: `lakefile.toml`（このリポジトリを読み込む）、
     `lean-toolchain`、`Proof/` フォルダ。
   * テストデータを取ってくる: nestest（CPU のテスト用 ROM）とそのログ、自作のテスト ROM。
   * 名前と値の表を作る: モデルに必要な値（RAM の番地、コードの 2 か所、いくつかの値）を、ROM と
     解析済みコードから取り出す。解析済みコードの命令を 1 つずつ ROM と照らし合わせるので
     （10,691 命令）、番地の間違いは見つかります。
2. このリポジトリをビルドする。
3. エミュレータを nestest のログと照らし合わせる（`smbrta nestest`）。
4. 証明のファイルを作る: `Proof/Rom.lean`（ROM、名前と値の表、1-1 の開始状態）と、定理ごとの
   ファイル（`smbrta gen-rom`、`smbrta gen-proofs`）。定理のファイルは、`Theorems/` の主張に
   `native_decide` を当てるだけです。
5. 非公開のプロジェクトをビルドする。ここで Lean が定理を確かめます。
6. 確かめた定理の一覧を表示する。

`proofProject` のファイルには ROM が入っているので、公開しないでください。

## 解析済みコード

doppelganger さんの「A Comprehensive Super Mario Bros. Disassembly」`SMBDIS.ASM` は、ROM の機械語を
6502 のアセンブリ言語の文字に戻し、RAM の変数や処理に名前（`Player_X_Speed`、`PlayerCtrlRoutine`
など）を付けたものです。このプロジェクトでは、`tools/smb-symbols.txt` にある名前の番地を調べるため
だけに使います。確かめたファイルは gist `1wErt3r/4048722`（<https://gist.github.com/1wErt3r/4048722>）
の https://gist.githubusercontent.com/1wErt3r/4048722/raw/7e8e9777a53a2f94fd968e79c891445a97a8ddde/SMBDIS.ASM で、SHA-256 は `e5c17c42783f430029ab90aa37c73d51c2c320898e533b3ff196dad38c50ae42` です。名前が同じなら、ほかの版でも使えます。
