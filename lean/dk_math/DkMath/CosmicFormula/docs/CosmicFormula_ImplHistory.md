# CosmicFormula Implements History

## CosmicFormula: Differential Coefficients Formalization

- 本履歴は、`CosmicFormula_Explanation_of_differential_coefficients.md` と
  `CosmicFormula_Design_Lean_Formal_of_differential_coefficients.md` を実装へ落とすための記録である。
- 記録様式は `CFBRC_Implements_History.md` に準拠し、各回で
  目的・内容・結論・失敗事例・備考・次課題を固定で残す。
- 初回は「実装前のワークスペース事前調査」と「段階的実装計画」の確定を行う。

## 記録内容テンプレート（例）

### 日時: YYYY/MM/DD HH:MM JST: 作業タイトル

1. 目的: この回で達成する具体目標
2. 内容:
   - 実施した調査/実装
   - 変更ファイル
   - ビルド/検証結果
3. 結論: この回で到達した状態
4. 失敗事例: 詰まった点・失敗要因・回避策
5. 備考: 設計判断や依存関係メモ
6. 次の課題: 次回着手する具体タスク

## 実装履歴

### 日時: 2026/03/20 16:48 JST: 微分係数宇宙式形式化の実装前調査と実装計画を確定

1. 目的: 実装前にワークスペースを調査し、差分核→微分橋→冪関数までの実装計画を確定する。
2. 内容:
   - 参照ドキュメントを読了:
     - `CosmicFormula_Explanation_of_differential_coefficients.md`
     - `CosmicFormula_Design_Lean_Formal_of_differential_coefficients.md`
   - ワークスペース事前調査:
     - `DkMath/CosmicFormula/docs/CosmicFormula_ImplHistory.md` は空で、履歴未開始。
     - `DkMath/Analysis` ディレクトリは未存在（設計書案のまま未着手）。
     - 既存 `CosmicFormula` 実装は主に `Defs/Basic/CosmicFormulaBasic/CosmicFormulaBinom` に集中。
     - 微分専用シンボル（`delta`, `cosmicKernel`, `powerKernel`）は現状 docs 内のみで Lean 実装なし。
     - 既存の関連 API:
       - `CosmicFormulaBasic.lean` に `(x+u)^2 - x*(x+2u) = u^2` 系の基本恒等式あり。
       - `CosmicFormulaBinom.lean` に `cosmic_id_csr'` など差分分解の土台あり。
       - `Samples/LPS/PowerSwapBranch.lean` に `HasDerivAt.tendsto_slope` 利用例あり。
   - 基線ビルド確認:
     - `lake build DkMath.CosmicFormula` 成功（2026/03/20）。
   - 実装計画（確定）:
     - Phase 1: 差分核基礎
       - 新規: `DkMath/CosmicFormula/CosmicDifferenceKernel.lean`
       - `delta`, `cosmicKernel`, `delta_add/sub/mul`, `cosmicKernel_eq` を実装。
     - Phase 2: derivative bridge
       - 新規: `DkMath/CosmicFormula/CosmicDerivativeBasic.lean`
       - `HasDerivAt` と punctured limit (`𝓝[≠] 0`) の橋渡し補題を実装。
       - 既存 mathlib 補題（例: slope 系）を優先再利用。
     - Phase 3: power kernel exact
       - 新規: `DkMath/CosmicFormula/CosmicDerivativePower.lean`
       - `powerKernel`, `(x+u)^d - x^d = u * powerKernel` を実装。
       - 既存 `CosmicFormulaBinom` の二項展開補題を再利用して重複証明を避ける。
     - Phase 4: power kernel limit + 微分定理
       - `tendsto_powerKernel_zero`, `hasDerivAt_pow_cosmic` を追加。
       - `j=0` 項と `j≥1` 項の有限和分解で極限証明を組み立てる。
     - Phase 5: 宇宙式本体との橋
       - 新規: `DkMath/CosmicFormula/CosmicFormulaDerivativeBridge.lean`
       - 一次差分核と二次補正核 (`cosmic_formula_unit`) の関係補題を整備。
     - 配線更新:
       - `DkMath/CosmicFormula/Basic.lean` に新規モジュール import を追加。
       - 必要なら `DkMath/CosmicFormula.lean` の入口を更新。
     - 検証方針:
       - 各 Phase 完了ごとに `lake build DkMath.CosmicFormula.<対象>` を実行。
       - 最終で `lake build DkMath.CosmicFormula` を再実行。
3. 結論: 実装前調査は完了し、現行コード構成に整合した 5 Phase 計画（差分核→微分橋→冪関数→橋渡し）を確定した。
4. 失敗事例:
   - 設計書案の `DkMath/Analysis/*` は現ワークスペースに存在せず、そのまま着手すると import 変更範囲が過大になる。
   - 回避として初期実装は `DkMath/CosmicFormula/*` 配下で閉じる方針に修正。
5. 備考:
   - 既存ビルドログに `ring` から `ring_nf` への提案メッセージはあるが、基線としてビルドは成功している。
   - 実装初回は「新規定義が docs 設計に一致すること」と「最小定理群が単体ビルド通過すること」を優先する。
6. 次の課題:
   - Phase 1 として `CosmicDifferenceKernel.lean` を新規作成し、`delta/cosmicKernel` 基礎補題群を実装する。
   - 入口 import を最小限で追加し、`lake build DkMath.CosmicFormula.CosmicDifferenceKernel` で初回通過を確認する。
