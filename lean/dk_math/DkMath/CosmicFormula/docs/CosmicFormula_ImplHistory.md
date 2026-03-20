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

      ```txt
       `tendsto_powerKernel_zero_punctured`
       + `cosmicKernel_pow_eq_powerKernel_of_ne_zero`
       + `hasDerivAt_of_tendsto_cosmicKernel`
      ```

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

### 日時: 2026/03/20 19:13 JST: `CosmicDerivativePolynomial` を追加し、多項式評価の微分を cosmic 形式へ一般化

1. 目的: 冪関数 case から一段抽象化し、`Polynomial ℝ` の評価関数 `fun y => p.eval y` について cosmic 微分 API を整備する。
2. 内容:
   - 新規ファイル追加:
     - `DkMath/CosmicFormula/CosmicDerivativePolynomial.lean`
   - 実装した定理:
     - `hasDerivAt_polynomial_eval_cosmic`
     - `tendsto_cosmicKernel_polynomial_eval`
     - `deriv_polynomial_eval_cosmic`
     - `hasDerivAt_polynomial_eval_finset_sum_cosmic`
   - import 配線更新:
     - `DkMath/CosmicFormula/Basic.lean` に
       `import DkMath.CosmicFormula.CosmicDerivativePolynomial` を追加。
   - 実装方針:
     - mathlib 既存 API（`Polynomial.hasDerivAt`, `Polynomial.deriv`）を起点にし、
       `tendsto_cosmicKernel_of_hasDerivAt` で cosmic kernel 極限へ接続。
     - 有限和版は `Finset.sum s P` へ畳み込んだ上で
       `Polynomial.eval_finset_sum` / `Polynomial.derivative_sum` で展開。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePolynomial` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
3. 結論: `CosmicDerivativePolynomial` 相当の多項式一般化が入り、
   「多項式評価の `HasDerivAt` / cosmic kernel limit / `deriv`」の 3 形態を利用可能にした。
4. 失敗事例:
   - `∑ ... in ...` 記法が新規ファイルでパース不安定だったため、
     `Finset.sum` 明示形で記述して回避。
   - `deriv` 補題で `unnecessarySimpa` 警告が出たため、`simp` 証明へ修正。
5. 備考:
   - 証明は既存 power case と同様に「mathlib 基本定理 + cosmic bridge」の薄い接着に寄せ、
     再利用性を優先した。
6. 次の課題:
   - 必要なら多項式の演算別 API（和・積・合成）を cosmic kernel 直結で補強する。
   - `CosmicFormula_Design_Lean_Formal_of_differential_coefficients.md` の段階表と
     今回追加 API の対応表を docs に追記する。

### 日時: 2026/03/20 20:15 JST: 多項式の演算別 API（和・積・合成）を cosmic kernel 直結で補強し、Lean 実装ガイド docs を開始

1. 目的: `CosmicDerivativePolynomial` を演算別に拡張し、同時に Lean 実装視点の説明書整備を開始する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDerivativePolynomial.lean`
     - `DkMath/CosmicFormula/docs/CosmicFormula_Lean_Implementation_Guide_of_differential_coefficients.md`（新規）
   - 演算別 API 追加（`CosmicDerivativePolynomial.lean`）:
     - 和:
       - `hasDerivAt_polynomial_eval_add_cosmic`
       - `tendsto_cosmicKernel_polynomial_eval_add`
       - `deriv_polynomial_eval_add_cosmic`
     - 積:
       - `hasDerivAt_polynomial_eval_mul_cosmic`
       - `tendsto_cosmicKernel_polynomial_eval_mul`
       - `deriv_polynomial_eval_mul_cosmic`
     - 合成:
       - `hasDerivAt_polynomial_eval_comp_cosmic`
       - `tendsto_cosmicKernel_polynomial_eval_comp`
       - `deriv_polynomial_eval_comp_cosmic`
   - 実装方針:
     - まず `(p + q)`, `(p * q)`, `(p.comp q)` 全体に
       `hasDerivAt_polynomial_eval_cosmic` を適用。
     - `Polynomial.eval_*` / `Polynomial.derivative_*` で演算別の形へ `simp` 展開。
     - 合成版は乗算順序差を `mul_comm` で正規化。
   - 新 docs 初版の内容:
     - 実装マップ（差分核 / bridge / power / polynomial）
     - Lean 実装パターン（`HasDerivAt` → `tendsto_cosmicKernel` → `deriv`）
     - 運用上注意（`Finset.sum` 明示形、`unnecessarySimpa` 対応）
     - 次の整備候補（有限和 API 拡張、設計書対応表）
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePolynomial` 成功。
3. 結論: 多項式演算 API は和・積・合成まで cosmic kernel 直結で利用可能になり、
   実装者向け docs の初版整備を開始した。
4. 失敗事例:
   - 合成版の初稿で微分係数の積順序が逆向き (`q' * p'`) となり型不一致。
   - `mul_comm` を `simp` に追加して目的形 (`p' * q'`) に正規化して解消。
5. 備考:
   - 演算別 API はすべて「`HasDerivAt` / `tendsto` / `deriv` の 3 形態」で揃えた。
6. 次の課題:
   - 有限和版 (`Finset.sum`) に対して `tendsto` / `deriv` 形 API を追加する。
   - 新 docs に「定理名 ↔ 設計書節」の対応表を追記し、参照性を高める。

### 日時: 2026/03/20 20:25 JST: 有限和 `Finset.sum` の `tendsto/deriv` API を追加し、設計書節対応表を docs へ追記

1. 目的: 多項式有限和 API を 3 形態（`HasDerivAt` / `tendsto` / `deriv`）で揃え、実装ガイドに「定理名 ↔ 設計書節」の参照表を追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDerivativePolynomial.lean`
     - `DkMath/CosmicFormula/docs/CosmicFormula_Lean_Implementation_Guide_of_differential_coefficients.md`
     - `DkMath/CosmicFormula/docs/CosmicFormula_ImplHistory.md`
   - 追加した定理（`CosmicDerivativePolynomial.lean`）:
     - `tendsto_cosmicKernel_polynomial_eval_finset_sum`
     - `deriv_polynomial_eval_finset_sum_cosmic`
   - 証明方針:
     - 既存 `hasDerivAt_polynomial_eval_finset_sum_cosmic` を起点に
       `tendsto_cosmicKernel_of_hasDerivAt` と `.deriv` で 2 形態を導出。
   - docs 追記:
     - 有限和 API の 3 形態を多項式一般化節に反映。
     - 「定理名 ↔ 設計書節 対応表」を新設し、
       差分核・bridge・power・多項式の主要定理を
       `CosmicFormula_Design_Lean_Formal_of_differential_coefficients.md` の節番号へ対応付け。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePolynomial` 成功。
     - `lake build DkMath.CosmicFormula` 成功。
3. 結論: 有限和版も 3 形態 API が揃い、実装ガイドは「定理から設計書へ遡れる」状態になった。
4. 失敗事例:
   - 特になし（既存補題連結で実装できた）。
5. 備考:
   - これで `CosmicDerivativePolynomial` では「単体・和・積・合成・有限和」の全てが
     `HasDerivAt` / `tendsto` / `deriv` の形で参照可能になった。
6. 次の課題:
   - 対応表に「未実装/非目標（設計書 §12〜§14）」のステータス列を追加する。
   - 一般関数側（多項式以外）へ演算 API を昇格させる際の依存方針を docs 化する。

### 日時: 2026/03/20 20:32 JST: `CosmicDifferenceKernel` の演算則を拡張（smul / Finset.sum / mul）

1. 目的: `CosmicDerivativePolynomial` の外側 API を支える内側構造核として、`delta` / `cosmicKernel` の演算則を強化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDifferenceKernel.lean`
     - `DkMath/CosmicFormula/docs/CosmicFormula_Lean_Implementation_Guide_of_differential_coefficients.md`
     - `DkMath/CosmicFormula/docs/CosmicFormula_ImplHistory.md`
   - 追加した補題（`CosmicDifferenceKernel.lean`）:
     - `delta_smul`
     - `cosmicKernel_smul`
     - `delta_finset_sum`
     - `cosmicKernel_finset_sum`
     - `cosmicKernel_mul`
   - 実装方針:
     - `delta` 側は `ring` と `delta_add` 再利用で線形性を追加。
     - `Finset.sum` 側は `Finset.induction_on` で `delta_add` / `cosmicKernel_add` に帰着。
     - `cosmicKernel_mul` は
       `delta_mul` → `add_div` → 各項の除算再配置（`div_eq_mul_inv`）で導出。
   - docs 更新:
     - 実装マップ（差分核層）へ新補題群を反映。
     - 「定理名 ↔ 設計書節」対応表へ新補題群を追加。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDifferenceKernel` 成功。
3. 結論: `delta` / `cosmicKernel` の演算則が「定数倍・有限和・積」まで拡張され、
   以後は多項式有限和の議論を kernel 側の構造から直接組み立てやすくなった。
4. 失敗事例:
   - `Finset` 帰納で `DecidableEq` インスタンス不足エラーが発生。
   - 各証明に `classical` を導入して解消。
   - `cosmicKernel_mul` で単純 `simp` が停止し、`calc` で分解して解消。
5. 備考:
   - 今回は API 追加に集中し、`CosmicDerivativePolynomial` 側の既存証明置換（kernel 直結化）は未着手。
6. 次の課題:
   - `CosmicDerivativePolynomial` の有限和 `tendsto/deriv` を
     `cosmicKernel_finset_sum` + 単項 kernel 補題ベースへ段階的に置き換える。
   - `cosmicKernel_monomial` を追加し、
     多項式を monomial 有限和として kernel レベルで展開する流れを実装する。

### 日時: 2026/03/20 20:40 JST: `cosmicKernel_monomial` を導入し、多項式 kernel を monomial 有限和へ展開

1. 目的: 次段の本丸として、`delta/cosmicKernel` の構造を使って monomial と多項式の kernel 展開を直接記述する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDerivativePolynomial.lean`
     - `DkMath/CosmicFormula/docs/CosmicFormula_Lean_Implementation_Guide_of_differential_coefficients.md`
     - `DkMath/CosmicFormula/docs/CosmicFormula_ImplHistory.md`
   - 追加した定理（`CosmicDerivativePolynomial.lean`）:
     - `cosmicKernel_monomial_of_ne_zero`
     - `cosmicKernel_eval_monomial_of_ne_zero`
     - `cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero`
   - 実装方針:
     - monomial 版は
       `cosmicKernel_smul` + `cosmicKernel_pow_eq_powerKernel_of_ne_zero` を直結。
     - 多項式版は
       `p.as_sum_range_C_mul_X_pow` で評価関数を monomial 有限和へ展開し、
       `cosmicKernel_finset_sum` + `cosmicKernel_monomial_of_ne_zero` で kernel 和へ移す。
   - docs 更新:
     - 実装マップ（多項式一般化層）に monomial/kernel 展開 API を追記。
     - 「定理名 ↔ 設計書節」対応表へ新定理を追加。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePolynomial` 成功。
3. 結論: `cosmicKernel` を monomial 有限和として扱う導線が実装され、
   多項式微分を「powerKernel の有限和」として読む準備が整った。
4. 失敗事例:
   - `p.as_sum_range_C_mul_X_pow` を `rw` で直接適用すると `natDegree` 周りで過剰書換えが発生。
   - `congrArg (fun q => q.eval y)` で評価に押し込む形へ変更して解消。
5. 備考:
   - `u = 0` では `cosmicKernel` と `powerKernel` の値が一般に一致しないため、
     新定理は `hu : u ≠ 0` 付きで実装した。
6. 次の課題:
   - `cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero` を起点に、
     有限和 `tendsto` の証明を「既存微分定理からの翻訳」依存を減らす方向で再構成する。
   - 必要なら `u = 0` を含む連続拡張版 API（別名で明示）を設計する。

### 日時: 2026/03/20 20:49 JST: 有限和 `tendsto` を kernel 分解ベースへ再構成し、`u=0` を含む連続拡張 API を導入

1. 目的:
   - `cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero` を起点に、
     有限和 `tendsto` の証明を「既存微分定理からの翻訳」依存を減らす方向へ再構成する。
   - `u = 0` を含む連続拡張版 API を別名で明示する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDerivativePolynomial.lean`
     - `DkMath/CosmicFormula/docs/CosmicFormula_Lean_Implementation_Guide_of_differential_coefficients.md`
     - `DkMath/CosmicFormula/docs/CosmicFormula_ImplHistory.md`
   - 追加した主定理/定義（`CosmicDerivativePolynomial.lean`）:
     - `polynomialKernelExt`
     - `cosmicKernel_polynomial_eval_eq_polynomialKernelExt_of_ne_zero`
     - `derivative_eval_eq_sum_range_coeff_mul_pow`
     - `continuous_polynomialKernelExt`
     - `polynomialKernelExt_zero`
     - `tendsto_polynomialKernelExt_zero`
     - `tendsto_polynomialKernelExt_zero_punctured`
     - `tendsto_cosmicKernel_polynomial_eval_via_powerKernel`
   - 証明再構成:
     - `tendsto_cosmicKernel_polynomial_eval_finset_sum` を
       `tendsto_cosmicKernel_polynomial_eval_via_powerKernel`（`p := Finset.sum s P`）経由へ差し替え。
     - これにより有限和 `tendsto` は

       ```txt
       `cosmicKernel = polynomialKernelExt (u ≠ 0)`
       + `polynomialKernelExt` の連続性
       + `powerKernel` 極限
       ```

       の流れで導出する形になった。
   - docs 更新:
     - 多項式一般化層へ `polynomialKernelExt` 系 API を追記。
     - 「定理名 ↔ 設計書節」対応表へ拡張 API と再構成定理を追加。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePolynomial` 成功。
3. 結論:
   - 有限和 `tendsto` は kernel 分解ベースで再構成され、
     `HasDerivAt` 翻訳依存を 1 段減らした。
   - `u=0` を含む連続拡張 API（`polynomialKernelExt`）が導入され、
     punctured 極限と full-neighborhood 極限の橋渡しが明示化された。
4. 失敗事例:
   - `continuous_polynomialKernelExt` 初稿で `Finset.continuous_sum` を使い未定義エラー。
   - `continuous_finset_sum` へ切替えて解消。
5. 備考:
   - 既存の `tendsto_cosmicKernel_polynomial_eval`（旧系）は互換維持で残し、
     新系は `..._via_powerKernel` 名で明示分離した。
6. 次の課題:
   - `tendsto_cosmicKernel_polynomial_eval` 本体を新系（`..._via_powerKernel`）へ統一するか判断。
   - `deriv` 側も `polynomialKernelExt` 起点で再構成する場合の API 設計を検討する。

### 日時: 2026/03/20 22:30 JST: `HasDerivAt` を `via_powerKernel` から再構成し、`polynomialKernelExt` の多項式専用性を docs 明示

1. 目的:
   - 分解/拡張/復帰の 3 層を維持したまま、`HasDerivAt` 側を `via_powerKernel` 系から直接導く。
   - `polynomialKernelExt` が多項式専用 API である点を docs で明確化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDerivativePolynomial.lean`
     - `DkMath/CosmicFormula/docs/CosmicFormula_Lean_Implementation_Guide_of_differential_coefficients.md`
     - `DkMath/CosmicFormula/docs/CosmicFormula_ImplHistory.md`
   - 追加した定理（`CosmicDerivativePolynomial.lean`）:
     - `hasDerivAt_polynomial_eval_cosmic_via_powerKernel`
     - `deriv_polynomial_eval_cosmic_via_powerKernel`
   - 再構成した既存定理:
     - `hasDerivAt_polynomial_eval_finset_sum_cosmic` の導出を
       `hasDerivAt_polynomial_eval_cosmic_via_powerKernel (p := Finset.sum s P)`
       ベースへ差し替え。
   - docs 明示:
     - `polynomialKernelExt` は
       「`powerKernel` の有限和として書ける多項式専用 extension」である旨を
       既知の運用上注意へ追記。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePolynomial` 成功。
3. 結論:
   - 推奨分岐 7.2（`HasDerivAt` 側の `via_powerKernel` 化）を反映し、
     多項式微分の導出経路はより direct になった。
4. 失敗事例:
   - `deriv_polynomial_eval_cosmic_via_powerKernel` 初稿で `unnecessarySimpa` 警告。
   - `simp` 形へ修正して解消。
5. 備考:
   - 互換性維持のため、既存 `hasDerivAt_polynomial_eval_cosmic` は残している。
6. 次の課題:
   - `tendsto_cosmicKernel_polynomial_eval` 本体を
     `tendsto_cosmicKernel_polynomial_eval_via_powerKernel` へ統一するか判断。
   - `hasDerivAt_polynomial_eval_cosmic` 本体も同系統へ寄せる場合の API 互換方針を決める。

### 日時: 2026/03/20 22:43 JST: `tendsto_cosmicKernel_polynomial_eval` 本体を `via_powerKernel` 系へ統一

1. 目的:
   - 7.1 方針として `tendsto_cosmicKernel_polynomial_eval` の canonical 実装を
     `tendsto_cosmicKernel_polynomial_eval_via_powerKernel` へ統一する。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/CosmicDerivativePolynomial.lean`
     - `DkMath/CosmicFormula/docs/CosmicFormula_Lean_Implementation_Guide_of_differential_coefficients.md`
     - `DkMath/CosmicFormula/docs/CosmicFormula_ImplHistory.md`
   - 実装変更:
     - 旧 bridge 直結証明を
       `tendsto_cosmicKernel_polynomial_eval_from_hasDerivAt` として分離。
     - `tendsto_cosmicKernel_polynomial_eval` は
       `tendsto_cosmicKernel_polynomial_eval_via_powerKernel` への委譲形へ更新。
   - docs 更新:
     - 多項式主要定理一覧と対応表に
       `tendsto_cosmicKernel_polynomial_eval_from_hasDerivAt` を追記し、
       旧系が補助位置づけであることを明確化。
   - ビルド検証:
     - `lake build DkMath.CosmicFormula.CosmicDerivativePolynomial` 成功。
3. 結論:
   - `tendsto_cosmicKernel_polynomial_eval` の本体は新系（kernel 分解 + 拡張 + 復帰）へ統一され、
     旧系は互換補助として保持される構造になった。
4. 失敗事例:
   - 特になし。
5. 備考:
   - API 名は維持したため、既存利用側の呼び出しは破壊していない。
6. 次の課題:
   - `hasDerivAt_polynomial_eval_cosmic` 本体も `..._via_powerKernel` へ統一するかを決める。
   - 統一方針決定後、旧系定理へ deprecation 方針を設けるか検討する。

### 日時: 2026/03/20 23:02 JST: canonical / legacy / direct / helper の status 管理を docs に導入

1. 目的:
   - 実装ガイドで旧系と新系の位置づけを明確化し、研究実装フェーズでの参照混線を防ぐ。
2. 内容:
   - 変更ファイル:
     - `DkMath/CosmicFormula/docs/CosmicFormula_Lean_Implementation_Guide_of_differential_coefficients.md`
     - `DkMath/CosmicFormula/docs/CosmicFormula_ImplHistory.md`
   - docs 更新:
     - 多項式主要定理一覧に `hasDerivAt_polynomial_eval_cosmic_from_mathlib` を追記。
     - 対応表に `Status` 列を追加し、
       `canonical` / `legacy bridge` / `direct decomposition` / `helper` を付与。
     - 運用上注意へ `Status` 列の読み方を明示。
3. 結論:
   - 「本流 API」と「比較参照用 API」の境界が文書上で明確化された。
4. 失敗事例:
   - 特になし。
5. 備考:
   - この段階では deprecated 化は実施せず、旧系は比較参照用に維持。
6. 次の課題:
   - 必要に応じて `hasDerivAt_polynomial_eval_cosmic_from_mathlib` /
     `tendsto_cosmicKernel_polynomial_eval_from_hasDerivAt` へ
     comment レベルの移行案内を付与する。
