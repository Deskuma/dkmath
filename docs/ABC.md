# ABC 予想（ABC Conjecture）形式化ドキュメント

本リポジトリでは、**ABC 予想**に関わる定義・定理・補題を Lean 4 で形式化し、数論的な補題や手法を構築しています。

このドキュメントでは、現状の成果物やモジュール構成、進捗状況・TODO を整理していきます。

---

## 1. 目的と背景

ABC 予想は、任意の正の整数 a, b, c について a + b = c を満たすときに、
「c の質（quality）が rad(abc)^{1+ε} を超える例は有限個である」という予想です。

本リポジトリでは、ABC 予想の形を Lean で定義し、関連する解析・数論的推論を形式化していくことを目的としています。

---

## 2. 主要ディレクトリとファイル

### 2.1. Lean コード本体

- `lean/dk_math/DkMath/ABC/` : ABC 関連の Lean コードをまとめたディレクトリ
  - `ABC*.lean` : 研究用の証明・補題群（番号付き）
  - `ABC.lean` / `ABC#Research.lean` : 主要な公開 API / 研究メモ等
  - `ABCError.lean` : 形式化中に扱うエラーや定義の検証用
  - `ABCWorking.lean`, `ABCSolvedProofSamples.lean` など：進捗メモやサンプル
  - `README.md` : 形式化の概要と定義（現状の主要ドキュメント）

### 2.2. ドキュメント

- `docs/ABC.md`（本ファイル）: 全体の進捗や構成をまとめるポータル
- `lean/dk_math/DkMath/ABC/docs/` : ABC モジュール固有の補助ドキュメント（現在空）

---

## 3. 進捗と現状の整理（暫定）

### 3.1. 主要定義

- `rad (n : ℕ)` : 素因数の積
- `quality (a b c : ℕ)` : 質（log 比）
- `abc_conjecture (ε : ℝ)` : ABC 予想の形式化
- `weak_abc_conjecture` : 質が 1+N を超える例が有限個である弱い形

（詳細は `lean/dk_math/DkMath/ABC/README.md` を参照）

### 3.2. 証明の骨子

- `[ABC0xx].lean` 系ファイルにおいて、
  - 素因数分解・rad に関する解析
  - logarithm を用いた質の評価
  - 密度議論 / 誤差項の制御（`adjBadCount` など）
  - 解析的補題（`quality_le_of_sqprod_pow_bound` 系）

- `ABC016`~ などの番号付きファイルは、議論の節点（lemmas/theorems）を段階的に構築している。

### 3.3. 未完部分の把握

- 証明の中で `sorry` が残っている箇所がある（特に解析的な log/sum の変換や、密度議論の部分）
- 章立てやモジュール分割が現状では散在しており、ドキュメントが追いついていない

---

## 4. ドキュメント整備の方向性

### 4.1. まずは「読む人のための地図」を用意する

- `docs/ABC.md` を入口として、主要ファイルと役割を整理する。
- `lean/dk_math/DkMath/ABC/README.md` を最新版の状況に合わせて更新し、具体的な定理名・証明戦略・依存関係を追記する。
- `lean/dk_math/DkMath/ABC/docs/` に、以下のようなドキュメントを追加する。
  - `Roadmap.md` : これまでの証明の流れと今後の TODO
  - `Glossary.md` : 専用用語・記法（`quality`, `adjBadCount` など）の意味
  - `ProofSketches/` : 主要結果の証明スケッチ（自然言語＋Leanコードの対応）

### 4.2. ドキュメントの更新運用

- コードを編集したら、対応するドキュメントも同じ PR / コミットで更新する。
- `TODO` セクションを明示し、`FIXME` などのマーカーを使って追跡しやすくする。

---

## 5. 次のステップ（提案）

1. `lean/dk_math/DkMath/ABC/README.md` の内容を最新版にアップデートし、
   - 定義・命題の一覧
   - 依存関係（どのファイルがどのファイルを import しているか）
   - 主要な “未完” 部分（`sorry` の位置）

2. `lean/dk_math/DkMath/ABC/docs/Roadmap.md` を作成し、
   - 各 `ABC###.lean` ファイルの役割をひとことでまとめる
   - 現状の「証明の流れ」を図解／リスト化する

3. 進捗管理のために、`docs/PROJECT_STATUS.md` のような形式で
   - ABC 予想関連の「現状と課題」セクションを追加する（例: `docs/PROJECT_STATUS.md#ABC`）

---

📌 まずはこの `docs/ABC.md` をベースに、

- 「どのファイルに何が書かれているか」
- 「どこまで証明が進んでいるか」
- 「次に何に着手すべきか」

を明確にしていくのが良いでしょう。

必要であれば、現状の `ABC*.lean` の依存関係や `sorry` の箇所を自動抽出して一覧化するスクリプトも作成できます。

---

## 6. 追加資料（リソース索引）

`lean/dk_math/DkMath/ABC/docs/__resource/` 以下には、作業ログや設計メモ、`sorry` 分析などのドキュメントが大量に蓄積されています。

- まずはこちらを参照してください: `lean/dk_math/DkMath/ABC/docs/ResourceIndex.md`（作業資料の横断索引）
- Telescoping 系の議論は `ABC-Telescope-Sorry-Analysis-2025-1013.md` / `ABC-Refactor-Plan-2025-1013.md` にまとまっています。

この索引を起点に、必要な情報をピックアップして進めてください。
