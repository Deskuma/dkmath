# KUS: Implementation History

## History Log

### 2026-03-14 / Work Unit 1. 内容把握

- KUS の主題は、通常の数体系で単一の `0` に潰れて失われる構造を、`(K, U, S_U)` という依存型構造として保持することだと確認。
- 特に零状態を `(0, U, S_U)` として扱い、観測的零 `toNat = 0` と構造保持零 `extract = (U, S_U)` を分離する設計方針を確認。
- README 上の初期実装対象は、`K : ℕ`、unit 依存 blueprint family、Nat 埋め込み、forget、extract、固定 fiber 上の可換モノイド、round-trip 定理に限定されていることを確認。
- 実装上の重要論点として、`Div` を早期導入せず `extract` を先に設計すること、全空間演算より固定 unit fiber の演算を優先すること、依存型として `S_U ∈ Blueprint(U)` を正面から扱うことを整理。
- repo 全体の流儀として、`Core` を中心に薄い補助モジュールを分け、入口ファイルで import 集約する構成が多いことを確認。KUS の README 案はその方針と整合する。
- 次段候補としては、`Unit.lean` と `Blueprint.lean` で依存型の土台を置き、`Core.lean` で最小 KUS 構造を定義し、続いて `NatEmbed.lean` と `Extract.lean` を設計する流れが自然と判断。
