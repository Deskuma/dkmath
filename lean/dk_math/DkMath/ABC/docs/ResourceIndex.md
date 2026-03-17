# ABC 形式化プロジェクト：リソース索引（Resource Index）

このドキュメントは、`lean/dk_math/DkMath/ABC/docs/__resource/` 以下に蓄積された「作業ログ」「分析メモ」「設計ノート」などの資料を横断的に参照し、
「どこに何が書いてあるのか」「次に何をすべきか」をすばやく把握するための入り口です。

---

## 1. まず読むべき主要資料（推奨順）

### 1.1. `ABC-map.md`

- **目的**: `ABC.lean`（および関連モジュール）の構造マップを示す。主要定義・補題群の依存関係が整理されている。
- **おすすめ度**: ⭐⭐⭐⭐⭐（全体像を掴むには最重要）

### 1.2. `ABC-Refactor-Plan-2025-1013.md`

- **目的**: Telescoping 系定理（`sum_pow_padicValNat_le_geom_*`）の再設計・リファクタ計画。
- **おすすめ度**: ⭐⭐⭐⭐☆（Telescoping/Layercake の中心部を改修する場合に必読）

### 1.3. `ABC-Telescope-Sorry-Analysis-2025-1013.md`

- **目的**: Telescoping 定理内の `sorry` を整理し、どこに数学的/設計的な問題があるかを分析したドキュメント。
- **おすすめ度**: ⭐⭐⭐⭐☆（「何が詰まっているか」を知るのに最速）

### 1.4. `ABC-Telescope-Implementation-2025-1013.md`

- **目的**: 上記分析に基づいた具体的な修正パッチ案（Lean コード片）を示す。
- **おすすめ度**: ⭐⭐⭐⭐☆（修正を実装する際の手順書として有用）

---

## 2. 主要テーマ／証明ラインごとの資料（カテゴリ別）

### A. Telescoping 系（∑ p^(t v_p(2n+1)) ≤ 3 (X+1)）

- **実装ファイル**: `lean/dk_math/DkMath/ABC/ABC025.lean`（`sum_pow_padicValNat_le_geom_log2_div_log3` など）
- **代表的な資料**:
  - `ABC-Refactor-Plan-2025-1013.md`
  - `ABC-Telescope-Sorry-Analysis-2025-1013.md`
  - `ABC-Telescope-Implementation-2025-1013.md`

### B. Layer‑cake / MGF 系（p‑進 MGF 余剰項評価）

- **実装ファイル**: `lean/dk_math/DkMath/ABC/ABC022.lean` ほか
- **関連資料**: `ABC-Telescope-Implementation-2025-1013.md` では Layer‑cake 版の修正も言及されている。

### C. Chernoff・確率論的境界系

- **実装ファイル**: `lean/dk_math/DkMath/ABC/ABCFinalChernoffPrototype.lean` など
- **進捗ログ**: `ABCFinalChernoff-progress-2025-1019-*.md` シリーズ

### D. Quality / ABC 本体（`quality` の上界）

- **実装ファイル**: `lean/dk_math/DkMath/ABC/ABCQualityLeOfNotBad.lean` ほか
- **進捗ログ**: `ABCFinal-progress-2025-10-01.md` など

---

## 3. いますぐ使える「優先度の高いタスク」リスト

### 3.1. Telescoping 定理の修正（最優先）

- **問題**: `t - 1 ≤ -log 2 / log 3` のような不等式が数学的に成立しない（`ABC-Telescope-Sorry-Analysis` で指摘）。
- **対応**: `t ≤ log2/log3` に対して「p^(t-1) ≤ 2/3」などの正しい評価を与える補題を用意し、定理の設計を修正する。
  - 参考補題: `rpow_t_sub_one_le_two_thirds` 等
- **対象コード**: `ABC025.lean` 内の `sum_pow_padicValNat_le_geom_*` 系

### 3.2. 数値評価（log 比・定数境界）の補題整備

- `3^(-log 2 / log 3) = 1/2` に基づく補題（`three_pow_neg_log2_div_log3_eq_half` など）を作り、数値不等式の `sorry` を置換する。
- **対象**: `ABC025.lean` ほか、`ABCFinalRealExpFactorizationLog.lean` など

### 3.3. 主要 `sorry` の 優先度付け（資料と対応）

- `ABC-Telescope-Sorry-Analysis`: `Category A`（数学的に不可能な命題）→ 設計変更必須
- `Category B`（証明補題が必要な数値評価）→ 補題を書いて埋める
- `Category C`（尾項評価の case 分岐）→ 小 X/大 X で分離して証明

---

## 4. 参考：主要 `sorry` が残るファイルと狙いどころ

| ファイル | 役割 | 代表的な未完箇所（コメント） |
|---|---|---|
| `ABC025.lean` | Telescoping / Sum-bound | `t - 1 ≤ -log 2 / log 3` の不等式、`(2X+2)^(log2/log3) ≤ X+1` など |
| `ABCQualityLeOfNotBad.lean` | ABC quality の上界 | log 分解や padicValNat の評価で `sorry` が多数 |
| `ABCFinalRealExpFactorizationLog.lean` | 解析的 log/exp factorization | 多数の `sorry` が残存（型変換・rpow 操作など） |
| `ABCFinalChernoffPrototype.lean` | Chernoff 型不等式の構造 | まずは `sorry` を「nested で defer」して構造を整えている |

---

## 5. 進め方の提案（このリポジトリでの「組み立て直し」）

1. **資料を “クイックスタート” 化する**
   - `ResourceIndex.md`（本ファイル）を入口とし、別途「TaskList.md」「ProofFlow.md」を作る。
2. **重要タスクを可視化する**
   - `sorry` の所在一覧（ファイル名 + 行番号 + 種類）を抽出し、優先度を付けて TODO 化。
3. **証明の主要ラインを「概念マップ」で整理する**
   - 例: Telescoping → Layercake → Chernoff → Quality → ABC main theorem
   - 各段階で必要な「キー補題」をリストアップして、コードと対応付ける。
4. **ドキュメントとコードを同時に更新する**
   - コードを編集したら、対応する資料（`Roadmap.md` など）も更新していく。

---

## 6. 追加支援（必要なら）

- **自動抽出**: `grep`/スクリプトで `sorry` を一覧化し、そのうち「数学的に解決が必要なもの」を分類する。
- **依存関係解析**: `ABC*.lean` の `import` 関係を可視化するスクリプトを作り、どのファイルを修正すると他に影響するかを把握する。
- **ProofFlow 図の自動生成**: `ABC-map.md` の Mermeid 図を拡張し、「何がどこで使われているか」を自動的に描く。

---

📌 **次の一歩**: まず `ABC-Telescope-Sorry-Analysis-2025-1013.md` を読み、そこに書かれている「お勧め修正（Phase 3）」を実際に `ABC025.lean` に適用してみるのが、最も即効性のあるアプローチです。
