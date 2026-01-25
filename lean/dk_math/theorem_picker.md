# Lean Theorem Picker

Lean ファイルから定義・定理・補題などを抽出し、Markdown に整形するツール。Lean 4 の LSP（Language Server Protocol）を使用して堅牢にパースしており、将来のバージョンアップにも対応する設計になっている。

## 使用方法

```bash
python theorem_picker.py input.lean [output.md]
```

- `input.lean`: 抽出対象の Lean ファイル
- `output.md`: 出力先 Markdown ファイル（デフォルト: `__Theorems.md`）
  - ファイルが存在すれば上書きされます

## 出力形式

````markdown
# Theorems

## ファイル名.lean

### 定義識別子1

```lean
（コード）
```

### 定義識別子2

```lean
（コード）
```

````

- `# Theorems`: 全体ヘッダ
- `## ファイル名.lean`: ファイル単位のヘッダ
- `### 識別子`: 各定義・定理・補題のヘッダ
- コードブロック内: Lean ソース

## 抽出ルール

### def（定義）

定義コード全体を含める。

### lemma / theorem（定理・補題）

最初に出現する `:= by` を含む行までを掲載し、それ以降は `...` で省略表示。

例：

```lean
lemma example_lemma : P := by
  ...
```

### instance（インスタンス）

完全なコードを掲載。

## 実装の特徴

### Lean LSP ベースの堅牢パース

- `lake env lean --server` で Lean 4 の公式パーサを利用
- `textDocument/documentSymbol` で正確なシンボル抽出
- 属性（`@[simp]` など）や修飾子（`noncomputable`）も正しく処理
- 改行位置の違いや複雑な構文にも対応

### 正規表現フォールバック廃止

Lean の構文は複雑で将来バージョンでも変わるため、正規表現ベースのフォールバックは廃止。常に LSP で厳密にパースする設計に統一。

### プロジェクトルート自動検出

`lakefile.toml` または `lean-toolchain` を探索して Lake プロジェクトルートを特定。LSP サーバを正しいコンテキストで起動。

## 技術詳細

### LeanLspClient クラス

LSP/JSON-RPC の簡易クライアント実装：

- `initialize` リクエストで接続初期化
- `textDocument/didOpen` でファイル内容を送信
- `textDocument/documentSymbol` で AST シンボル取得
- サーバー側リクエスト（`workspace/inlayHint/refresh` など）にも自動応答
- `shutdown` / `exit` で正常終了

### シンボル抽出フロー

1. ソースを LSP サーバに送信
2. documentSymbol でシンボルリスト（kind、range など）を取得
3. kind でフィルタ（宣言のみ、モジュール・名前空間は除外）
4. range でソースをスライス
5. ファイル内の出現順でソート
6. Markdown に整形

## テスト

- `test_theorem_picker.py` にユニットテストを実装
- 様々な定義スタイル・属性・複雑な構文に対応

### テスト実行方法

```bash
python -m pytest test_theorem_picker.py -v
```

## 動作要件

- Python 3.8 以上
- Lean 4 環境（`lake env lean --server` が実行可能）
- Lake プロジェクト（`lakefile.toml` 必須）

## ログ

### 2026-01-24

#### LSP ベース化・シンプル化

- LSP 専用実装に統一、正規表現フォールバック廃止
- Lean の言語サーバを活用した堅牢なパース
- `--use-lsp` オプション削除（常に LSP 使用）
- 不要な regex helper 関数削除
- コード簡潔化（約150行削減）
