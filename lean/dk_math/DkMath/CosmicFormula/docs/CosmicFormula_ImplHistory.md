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

### 日時: 2026/03/20 16:53 JST: Phase 1 実装（差分核 `delta` / `cosmicKernel` の基礎補題群を追加）

1. 目的: 実装計画の Phase 1 として、宇宙式微分の最小コア（差分演算子と差分商核）を Lean コード化する。
2. 内容:
   - 新規ファイル追加:
     - `DkMath/CosmicFormula/CosmicDifferenceKernel.lean`
   - 実装した定義:
     - `delta (f : ℝ → ℝ) (x u : ℝ) : ℝ := f (x + u) - f x`
     - `cosmicKernel (f : ℝ → ℝ) (x u : ℝ) : ℝ := delta f x u / u`
   - 実装した補題:
     - `delta_zero_right`
     - `delta_add`
     - `delta_sub`
     - `delta_mul`
     - `cosmicKernel_eq`
     - `cosmicKernel_add`
     - `cosmicKernel_sub`
   - import 配線更新:
     - `DkMath/CosmicFormula/Basic.lean` に
       `import DkMath.CosmicFormula.CosmicDifferenceKernel` を追加。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDifferenceKernel` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
3. 結論: Phase 1 の最小実装は完了し、差分核 API が `DkMath.CosmicFormula` 系に組み込まれた。
4. 失敗事例:
   - 新規ファイル先頭コメントを `/* ... */` で書き、Lean がパース失敗。
   - `Real` の割り算を含む定義で `noncomputable` 指定が必要だった。
   - `noncomputable section` の `end` 漏れで scope エラーが発生。
5. 備考:
   - いずれも局所修正で解消し、最終ビルドは安定通過した。
   - 補題群は設計書の Phase 1 要件（差分・核の基礎）に一致している。
6. 次の課題:
   - Phase 2 として `CosmicDerivativeBasic.lean` を追加し、
     `HasDerivAt` と `𝓝[≠] (0 : ℝ)` 極限を結ぶ橋渡し補題へ着手する。
   - 既存の `HasDerivAt.tendsto_slope` 系 API を再利用して証明骨格を固定する。

### 日時: 2026/03/20 17:16 JST: Phase 2 実装（`HasDerivAt` と cosmic kernel 極限の橋渡し定理を追加）

1. 目的: `HasDerivAt` を宇宙式差分核 `cosmicKernel` の punctured-limit で記述する基本橋を実装する。
2. 内容:
   - 新規ファイル追加:
     - `DkMath/CosmicFormula/CosmicDerivativeBasic.lean`
   - 実装した主要定理:
     - `hasDerivAt_iff_tendsto_cosmicKernel`
     - `tendsto_cosmicKernel_of_hasDerivAt`
     - `hasDerivAt_of_tendsto_cosmicKernel`
     - `hasDerivAt_id_cosmic`
     - `tendsto_cosmicKernel_id`
     - `hasDerivAt_const_cosmic`
     - `tendsto_cosmicKernel_const`
   - 証明方針:
     - mathlib の `hasDerivAt_iff_tendsto_slope_zero` を直接利用し、
       `cosmicKernel` 形式へ `simpa` で橋渡し。
   - import 配線更新:
     - `DkMath/CosmicFormula/Basic.lean` に
       `import DkMath.CosmicFormula.CosmicDerivativeBasic` を追加。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativeBasic` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
3. 結論: Phase 2 目標の中核である
   「`HasDerivAt` ↔ cosmic kernel の punctured-limit」が Lean 実装として成立した。
4. 失敗事例:
   - `𝓝[≠]` / `𝓝` 記法がこのファイルの記法スコープで解決されずパース失敗。
   - `Tendsto` を unqualified に書いて識別子未解決。
   - `Filter.nhds` も本環境では未解決で、`nhds` へ修正が必要だった。
5. 備考:
   - 記法依存を避けるため、最終版は
     `nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ))`
     と `Filter.Tendsto` / `nhds` を採用した。
   - この形は後続 Phase（power kernel）でも再利用しやすい。
6. 次の課題:
   - Phase 3 として `CosmicDerivativePower.lean` を追加し、
     `powerKernel` と
     `(x+u)^d - x^d = u * powerKernel`
     の exact factorization を実装する。
   - 既存 `CosmicFormulaBinom` の二項展開補題を優先再利用し、証明重複を回避する。

### 日時: 2026/03/20 17:19 JST: Phase 3 実装（`powerKernel` と exact factorization を追加）

1. 目的: power case の exact 層を実装し、差分冪を `u * powerKernel` に因数分解する。
2. 内容:
   - 新規ファイル追加:
     - `DkMath/CosmicFormula/CosmicDerivativePower.lean`
   - 実装した定義・定理:
     - `powerKernel`
     - `powerKernel_eq_GN_swap`
     - `sub_pow_eq_u_mul_powerKernel`
     - `sub_eq_u_mul_powerKernel`（alias）
     - `cosmicKernel_pow_eq_powerKernel_of_ne_zero`
   - 証明方針:
     - 既存 `DkMath.CosmicFormulaBinom.cosmic_id_csr'` を
       `x := u, u := x` で再利用し、
       `(x+u)^d - x^d` の分解へ接続。
     - `powerKernel` は `GN d u x` との一致補題
       `powerKernel_eq_GN_swap` を介して整理。
   - import 配線更新:
     - `DkMath/CosmicFormula/Basic.lean` に
       `import DkMath.CosmicFormula.CosmicDerivativePower` を追加。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePower` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
3. 結論: Phase 3 の exact 要件
   「`(x+u)^d - x^d = u * powerKernel`」を Lean 実装として確立した。
4. 失敗事例:
   - `∑ ... in ...` 記法がこの新規ファイルでパース失敗し、`Finset.sum` 明示形へ変更。
   - `Basic.lean` 更新時に一度パス指定を誤った。
   - `simp ... using` を使って構文エラーを起こし、`exact mul_div_cancel_left₀ ...` に修正。
5. 備考:
   - 既存 Binom 補題を再利用したことで、power case の証明重複を抑制できた。
   - `cosmicKernel_pow_eq_powerKernel_of_ne_zero` により、次フェーズの極限定理へ直結可能な形になった。
6. 次の課題:
   - Phase 4 として `tendsto_powerKernel_zero` と `hasDerivAt_pow_cosmic` を実装する。
   - `j=0` 項と `j≥1` 項の有限和分解（高次項消滅）で極限証明を構成する。

### 日時: 2026/03/20 17:23 JST: Phase 4 実装（`hasDerivAt_pow_cosmic` と `tendsto_powerKernel_zero` を追加）

1. 目的: power case の limit/derivative 層を実装し、Phase 3 の exact 核を微分定理へ接続する。
2. 内容:
   - 新規ファイル追加:
     - `DkMath/CosmicFormula/CosmicDerivativePowerLimit.lean`
   - 実装した定理:
     - `hasDerivAt_pow_cosmic`
     - `tendsto_powerKernel_zero`（punctured 近傍版）
   - 証明方針:
     - `hasDerivAt_pow_cosmic` は mathlib `hasDerivAt_pow` から `simpa` で導出。
     - `tendsto_powerKernel_zero` は
       `tendsto_cosmicKernel_of_hasDerivAt` と
       `cosmicKernel_pow_eq_powerKernel_of_ne_zero` を
       `tendsto_nhdsWithin_congr` で接続して導出。
   - import 配線更新:
     - `DkMath/CosmicFormula/Basic.lean` に
       `import DkMath.CosmicFormula.CosmicDerivativePowerLimit` を追加。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePowerLimit` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
3. 結論: Phase 4 要件（冪関数微分定理 + power kernel の punctured limit）を実装完了した。
4. 失敗事例:
   - `tendsto_nhdsWithin_congr` 呼び出しで `f/g` の推論が曖昧になり失敗。
   - `f := cosmicKernel` / `g := powerKernel` を明示して解決。
5. 備考:
   - `tendsto_powerKernel_zero` は現時点で punctured 近傍版として実装。
   - 全近傍版（`nhds 0`）へ強化する場合は `u=0` 点での値一致と連続性の補題追加で拡張可能。
6. 次の課題:
   - Phase 5 として `CosmicFormulaDerivativeBridge.lean` を追加し、
     一次差分核と二次補正核（`cosmic_formula_unit`）の橋渡し補題を整備する。

### 日時: 2026/03/20 17:26 JST: Phase 5 実装（一次差分核と二次補正核の bridge 補題を追加）

1. 目的: 一次差分核（`delta`, `powerKernel 2`）と宇宙式本体の二次補正核（`cosmic_formula_unit`）を明示的に接続する。
2. 内容:
   - 新規ファイル追加:
     - `DkMath/CosmicFormula/CosmicFormulaDerivativeBridge.lean`
   - 実装した主要補題:
     - `delta_pow_two_eq_u_mul_powerKernel_two`
     - `cosmic_formula_unit_eq_delta_pow_two_sub_two_mul`
     - `cosmic_formula_unit_eq_u_mul_powerKernel_two_sub_two_mul`
     - `cosmic_formula_unit_eq_u_mul_powerKernel_two_gap`
     - `cosmic_formula_unit_eq_u_sq_from_derivative_bridge`
   - import 配線更新:
     - `DkMath/CosmicFormula/Basic.lean` に
       `import DkMath.CosmicFormula.CosmicFormulaDerivativeBridge` を追加。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicFormulaDerivativeBridge` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
     - `lake build DkMath` 成功（既存他モジュール由来の warning / sorry 表示は継続）。
3. 結論: Phase 5 目標の
   「一次差分核と二次補正核の橋渡し」が Lean 補題として実装完了した。
4. 失敗事例:
   - 1箇所 `simpa` の不要警告が出たため `exact` へ置換して解消。
5. 備考:
   - これで当初計画した 5 Phase（差分核→微分橋→power exact→power limit→二次橋渡し）は一通り実装済み。
6. 次の課題:
   - `tendsto_powerKernel_zero` を全近傍版（`nhds 0`）へ強化するか判断する。
   - 必要なら多項式一般化（`CosmicDerivativePolynomial` 相当）へ進む。

### 日時: 2026/03/20 17:50 JST: `tendsto_powerKernel_zero` を全近傍版（`nhds 0`）へ強化

1. 目的: `tendsto_powerKernel_zero` のフィルタを punctured 近傍から全近傍へ強化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDerivativePowerLimit.lean`
   - 変更点:
     - `tendsto_powerKernel_zero` の型を
       `nhdsWithin (0) ({0}ᶜ)` から `nhds (0)` に更新。
     - 証明を「punctured bridge」から「連続性 + `u=0` 値評価」へ置換:
       - `hcont : Continuous (fun u => powerKernel d x u)` を `continuity` で構成
       - `hzero : powerKernel d x 0 = (d:ℝ) * x^(d-1)` を `d` の場合分けで証明
       - `hcont.tendsto 0` を `hzero` で書換えて目標を導出
     - 互換補題として
       `tendsto_powerKernel_zero_punctured` を追加
       （`mono_left nhdsWithin_le_nhds` で導出）。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePowerLimit` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
3. 結論: `tendsto_powerKernel_zero` は設計書どおり全近傍版（`nhds 0`）で成立した。
4. 失敗事例:
   - 初回の `hzero` 証明で `simp` が進まず失敗。
   - `Finset.sum_eq_single` による `d` 場合分けへ切替えて解消。
5. 備考:
   - 既存利用に配慮して punctured 版は補題として残した。
6. 次の課題:
   - 必要なら `hasDerivAt_pow_cosmic` の証明を cosmic kernel 経由の構成へ統一し、説明文書との対応をさらに強化する。

### 日時: 2026/03/20 18:54 JST: `CosmicDerivativePowerLimit` を 3 層APIへ整理し、`hasDerivAt_pow_cosmic` を構成版へ更新

1. 目的: 実装を再利用しやすい形へ整理し、`hasDerivAt_pow_cosmic` を cosmic kernel フローで導出する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDerivativePowerLimit.lean`
   - API 整理（3 層分割）:
     - `continuous_powerKernel`
     - `powerKernel_zero`
     - `tendsto_powerKernel_zero`
   - `tendsto_powerKernel_zero` は次の 1 行構成へ整理:
     - `simpa [powerKernel_zero] using (continuous_powerKernel d x).tendsto 0`
   - 互換補題維持:
     - `tendsto_powerKernel_zero_punctured`
   - 次段実装:
     - `hasDerivAt_pow_cosmic` を `simpa hasDerivAt_pow` から置換し、
       `tendsto_powerKernel_zero_punctured`
       + `cosmicKernel_pow_eq_powerKernel_of_ne_zero`
       + `hasDerivAt_of_tendsto_cosmicKernel`
       の接続で構成的に証明。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePowerLimit` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
3. 結論: `tendsto_powerKernel_zero` は整理された API 上に再配置され、`hasDerivAt_pow_cosmic` は説明資料と一致する証明フローへ更新された。
4. 失敗事例:
   - `powerKernel_zero` 初版で `simp` が進まず失敗。
   - `d` 場合分け + `Finset.sum_eq_single` に切替えて安定化。
5. 備考:
   - 今回の整理で、`powerKernel` 系 API の独立再利用性が向上した。
6. 次の課題:
   - 必要なら `CosmicDerivativePolynomial` 相当の多項式一般化へ進む。
