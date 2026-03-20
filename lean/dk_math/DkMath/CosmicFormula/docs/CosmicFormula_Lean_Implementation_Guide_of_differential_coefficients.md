# CosmicFormula Lean 実装ガイド（微分係数編）

## 1. 目的

この文書は、`CosmicFormula_Explanation_of_differential_coefficients.md`（概念）と
`CosmicFormula_Design_Lean_Formal_of_differential_coefficients.md`（設計）を、
現在の Lean 実装へ対応付けるための実装者向けガイドである。

- 対象読者: `DkMath/CosmicFormula` 配下を拡張する実装者
- 対象範囲: 差分核 `cosmicKernel` を起点とした 1 変数実関数の微分 API
- 方針: 「定義 → bridge → exact 展開 → limit → HasDerivAt/deriv」の順で追えるように整理

---

## 2. 実装マップ（2026/03/20 時点）

### 2.1 差分核の定義層

- ファイル: `DkMath/CosmicFormula/CosmicDifferenceKernel.lean`
- 主要定義:
  - `delta (f : ℝ → ℝ) (x u : ℝ) := f (x + u) - f x`
  - `cosmicKernel (f : ℝ → ℝ) (x u : ℝ) := delta f x u / u`
- 主要補題:
  - `delta_add`, `delta_sub`, `delta_smul`, `delta_mul`, `delta_finset_sum`
  - `cosmicKernel_add`, `cosmicKernel_sub`, `cosmicKernel_smul`,
    `cosmicKernel_finset_sum`, `cosmicKernel_mul`

### 2.2 微分 bridge 層（mathlib 接続）

- ファイル: `DkMath/CosmicFormula/CosmicDerivativeBasic.lean`
- 主要定理:
  - `hasDerivAt_iff_tendsto_cosmicKernel`
  - `tendsto_cosmicKernel_of_hasDerivAt`
  - `hasDerivAt_of_tendsto_cosmicKernel`

### 2.3 冪関数 exact/limit 層

- ファイル:
  - `DkMath/CosmicFormula/CosmicDerivativePower.lean`
  - `DkMath/CosmicFormula/CosmicDerivativePowerLimit.lean`
- 主要定理:
  - `sub_pow_eq_u_mul_powerKernel`
  - `cosmicKernel_pow_eq_powerKernel_of_ne_zero`
  - `continuous_powerKernel`
  - `powerKernel_zero`
  - `tendsto_powerKernel_zero`
  - `hasDerivAt_pow_cosmic`

### 2.4 多項式一般化層

- ファイル: `DkMath/CosmicFormula/CosmicDerivativePolynomial.lean`
- 主要定理（単体）:
  - `hasDerivAt_polynomial_eval_cosmic`
  - `hasDerivAt_polynomial_eval_cosmic_from_mathlib`
  - `tendsto_cosmicKernel_polynomial_eval`
  - `tendsto_cosmicKernel_polynomial_eval_from_hasDerivAt`
  - `deriv_polynomial_eval_cosmic`
  - `deriv_polynomial_eval_cosmic_from_mathlib`
  - `cosmicKernel_monomial_of_ne_zero`
  - `cosmicKernel_eval_monomial_of_ne_zero`
  - `cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero`
  - `polynomialKernelExt`
  - `cosmicKernel_polynomial_eval_eq_polynomialKernelExt_of_ne_zero`
  - `continuous_polynomialKernelExt`
  - `polynomialKernelExt_zero`
  - `tendsto_polynomialKernelExt_zero`
  - `tendsto_cosmicKernel_polynomial_eval_via_powerKernel`
  - `hasDerivAt_polynomial_eval_cosmic_via_powerKernel`
  - `deriv_polynomial_eval_cosmic_via_powerKernel`
- 演算別 API:
  - 和: `hasDerivAt_polynomial_eval_add_cosmic`,
    `tendsto_cosmicKernel_polynomial_eval_add`,
    `deriv_polynomial_eval_add_cosmic`
  - 積: `hasDerivAt_polynomial_eval_mul_cosmic`,
    `tendsto_cosmicKernel_polynomial_eval_mul`,
    `deriv_polynomial_eval_mul_cosmic`
  - 合成: `hasDerivAt_polynomial_eval_comp_cosmic`,
    `tendsto_cosmicKernel_polynomial_eval_comp`,
    `deriv_polynomial_eval_comp_cosmic`
- 有限和拡張:
  - `hasDerivAt_polynomial_eval_finset_sum_cosmic`
  - `tendsto_cosmicKernel_polynomial_eval_finset_sum`
  - `deriv_polynomial_eval_finset_sum_cosmic`

---

## 3. Lean 実装パターン

### 3.1 基本パターン（推奨）

1. `HasDerivAt` を先に確立する。
2. `tendsto_cosmicKernel_of_hasDerivAt` で cosmic kernel の極限へ落とす。
3. 必要なら `(HasDerivAt ...).deriv` で `deriv` 形を得る。

この順に統一すると、証明コードが短くなり API の見通しが良い。

### 3.2 演算別パターン

- 和/積/合成は、まず `(p + q)`, `(p * q)`, `(p.comp q)` 全体で
  `hasDerivAt_polynomial_eval_cosmic` を適用する。
- その後 `Polynomial.eval_*` / `Polynomial.derivative_*` の `simp` 展開で
  目的の演算別形へ正規化する。
- 合成では係数の順序差（`a * b` と `b * a`）が出るため、
  `mul_comm` を `simp` セットに含めて正規化すると安定する。

---

## 4. 既知の運用上注意

- 一部環境で `∑ ... in ...` 記法のパースが不安定なため、
  新規ファイルでは `Finset.sum` 明示形が安全。
- `simpa` は linter により `unnecessarySimpa` 警告になることがある。
  自明同値だけなら `simp` へ寄せる。
- `polynomialKernelExt` は多項式専用 API である。
  `powerKernel` の有限和として明示定義できることを使っているため、
  任意関数への一般化 API とは分けて扱う。
- 対応表の `Status` は次の意味:
  `canonical`（公開本流） / `legacy bridge`（互換参照） /
  `direct decomposition`（分解に立脚した中核） / `helper`（補助 API）。

---

## 5. 定理名 ↔ 設計書節 対応表

| Lean 定理/定義 | 実装ファイル | 設計書節 | Status |
|---|---|---|---|
| `delta`, `cosmicKernel` | `CosmicDifferenceKernel.lean` | §4 | `canonical` |
| `delta_add`, `delta_sub`, `delta_smul`, `delta_mul`, `delta_finset_sum` | `CosmicDifferenceKernel.lean` | §5.1 | `helper` |
| `cosmicKernel_eq`, `cosmicKernel_add`, `cosmicKernel_smul`, `cosmicKernel_finset_sum`, `cosmicKernel_mul` | `CosmicDifferenceKernel.lean` | §5.2 | `helper` |
| `hasDerivAt_iff_tendsto_cosmicKernel` | `CosmicDerivativeBasic.lean` | §6 | `canonical` |
| `sub_pow_eq_u_mul_powerKernel` | `CosmicDerivativePower.lean` | §7 | `direct decomposition` |
| `tendsto_powerKernel_zero` | `CosmicDerivativePowerLimit.lean` | §8 | `canonical` |
| `hasDerivAt_pow_cosmic` | `CosmicDerivativePowerLimit.lean` | §9 | `canonical` |
| `cosmic_formula_unit_eq_u_sq_from_derivative_bridge` | `CosmicFormulaDerivativeBridge.lean` | §10 | `helper` |
| `hasDerivAt_polynomial_eval_cosmic` | `CosmicDerivativePolynomial.lean` | §3.5 / §11.4 | `canonical` |
| `hasDerivAt_polynomial_eval_cosmic_from_mathlib` | `CosmicDerivativePolynomial.lean` | §6 / §11.4 | `legacy bridge` |
| `tendsto_cosmicKernel_polynomial_eval` | `CosmicDerivativePolynomial.lean` | §8 / §11.4 | `canonical` |
| `tendsto_cosmicKernel_polynomial_eval_from_hasDerivAt` | `CosmicDerivativePolynomial.lean` | §6 / §11.4 | `legacy bridge` |
| `deriv_polynomial_eval_cosmic` | `CosmicDerivativePolynomial.lean` | §3.5 / §11.4 | `canonical` |
| `deriv_polynomial_eval_cosmic_from_mathlib` | `CosmicDerivativePolynomial.lean` | §6 / §11.4 | `legacy bridge` |
| `cosmicKernel_monomial_of_ne_zero` | `CosmicDerivativePolynomial.lean` | §3.5 / §11.4 | `direct decomposition` |
| `cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero` | `CosmicDerivativePolynomial.lean` | §3.5 / §11.4 | `direct decomposition` |
| `polynomialKernelExt`, `continuous_polynomialKernelExt`, `polynomialKernelExt_zero` | `CosmicDerivativePolynomial.lean` | §2.2 / §8 / §11.4 | `helper` |
| `tendsto_polynomialKernelExt_zero`, `tendsto_cosmicKernel_polynomial_eval_via_powerKernel` | `CosmicDerivativePolynomial.lean` | §8 / §11.4 | `direct decomposition` |
| `hasDerivAt_polynomial_eval_cosmic_via_powerKernel`, `deriv_polynomial_eval_cosmic_via_powerKernel` | `CosmicDerivativePolynomial.lean` | §6 / §11.4 | `direct decomposition` |
| `hasDerivAt_polynomial_eval_finset_sum_cosmic` | `CosmicDerivativePolynomial.lean` | §11.4 | `canonical` |
| `tendsto_cosmicKernel_polynomial_eval_finset_sum` | `CosmicDerivativePolynomial.lean` | §11.4 | `canonical` |
| `deriv_polynomial_eval_finset_sum_cosmic` | `CosmicDerivativePolynomial.lean` | §11.4 | `canonical` |

## 6. 次の整備候補

- 多項式 API から一般関数 API（和・積・合成）への橋渡し節を追加する。
- 対応表に設計書の将来節（例: §12〜§14）との「未実装/非目標」状態を明示する。
