/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import Mathlib.Algebra.Polynomial.Derivative

#print "file: DkMath.Lib.Algebra.FiniteProductWronskian"

/-!
# 有限分数和の共通分母 Wronskian

有限個の有理式

`X + Σᵢ Nᵢ / Dᵢ`

を一つの分子 `A` と分母 `D` にまとめるとき、各因子を除いた積
`Eᵢ = ∏ⱼ≠ᵢ Dⱼ` を使って

`D = ∏ᵢ Dᵢ`, `A = X D + Σᵢ Nᵢ Eᵢ`

と書ける。本ファイルは、この表示の Wronskian を各局所 Wronskian へ
分解する一般多項式恒等式を証明する。有限核や楕円曲線の仮定は不要であり、
Vélu 補正項を半核全体へ持ち上げるための代数層だけを担当する。
-/

namespace DkMath.Lib.Algebra.FiniteProductWronskian

open Polynomial
open scoped BigOperators

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-! ## 共通分母の構成 -/

/-- `i` を除いた分母因子の積 `Eᵢ = ∏ j ∈ s.erase i, D j`。 -/
noncomputable def erasedProduct (s : Finset ι) (D : ι → R[X]) (i : ι) : R[X] :=
  ∏ j ∈ s.erase i, D j

/-- 全分母の積 `D = ∏ i ∈ s, D i`。 -/
noncomputable def commonDenominator (s : Finset ι) (D : ι → R[X]) : R[X] :=
  ∏ i ∈ s, D i

/-- `X D + Σᵢ Nᵢ Eᵢ` として構成した共通分子。 -/
noncomputable def commonNumerator (s : Finset ι)
    (N D : ι → R[X]) : R[X] :=
  X * commonDenominator s D + ∑ i ∈ s, N i * erasedProduct s D i

/-- 有限積は、選んだ因子と除去積の積へ分解できる。 -/
theorem commonDenominator_eq_factor_mul_erasedProduct
    (s : Finset ι) (D : ι → R[X]) {i : ι} (hi : i ∈ s) :
    commonDenominator s D = D i * erasedProduct s D i := by
  unfold commonDenominator erasedProduct
  rw [Finset.mul_prod_erase s D hi]

/-! ## Wronskian の有限分解 -/

/-- 共通分母表示の Wronskian は局所 Wronskian の二乗重み付き和へ分解する。

`A = X D + Σᵢ Nᵢ Eᵢ`、`D = Dᵢ Eᵢ` とすると、

`A' D - A D' = D² + Σᵢ Eᵢ² (Nᵢ' Dᵢ - Nᵢ Dᵢ')`。

各項の微分を展開した後、`D = Dᵢ Eᵢ` を因子分解として使い、
可換環上の `ring` で閉じる。 -/
theorem commonNumerator_wronskian_eq
    (s : Finset ι) (N D : ι → R[X]) :
    (commonNumerator s N D).derivative * commonDenominator s D -
        commonNumerator s N D * (commonDenominator s D).derivative =
      (commonDenominator s D) ^ 2 +
        ∑ i ∈ s, (erasedProduct s D i) ^ 2 *
          ((N i).derivative * D i - N i * (D i).derivative) := by
  classical
  unfold commonNumerator
  simp only [derivative_add, derivative_mul, derivative_X, one_mul,
    derivative_sum]
  ring_nf
  rw [Finset.mul_sum, Finset.mul_sum]
  ring_nf
  calc
    _ = commonDenominator s D ^ 2 +
        ((∑ i ∈ s, (commonDenominator s D * derivative (N i) * erasedProduct s D i +
            commonDenominator s D * N i * derivative (erasedProduct s D i))) -
          ∑ i ∈ s, (derivative (commonDenominator s D) * N i * erasedProduct s D i)) := by
      ring
    _ = commonDenominator s D ^ 2 +
        ∑ i ∈ s, (commonDenominator s D * derivative (N i) * erasedProduct s D i +
          commonDenominator s D * N i * derivative (erasedProduct s D i) -
          derivative (commonDenominator s D) * N i * erasedProduct s D i) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [commonDenominator_eq_factor_mul_erasedProduct s D hi]
      simp only [erasedProduct]
      simp only [derivative_mul]
      ring

/-- 局所 Wronskian の既知表示を共通分母恒等式へ代入する橋。

`commonNumerator_wronskian_eq` の各局所項を、別に与えた多項式 `Z i` へ
置き換えた形である。Vélu 補正では `Z i = (X-aᵢ) Zᵢ` を渡すだけで、
有限積の代数展開と曲線固有の局所計算を分離できる。 -/
theorem commonNumerator_wronskian_eq_of_local
    (s : Finset ι) (N D Z : ι → R[X])
    (hZ : ∀ i ∈ s,
      (N i).derivative * D i - N i * (D i).derivative = Z i) :
    (commonNumerator s N D).derivative * commonDenominator s D -
        commonNumerator s N D * (commonDenominator s D).derivative =
      (commonDenominator s D) ^ 2 +
        ∑ i ∈ s, (erasedProduct s D i) ^ 2 * Z i := by
  rw [commonNumerator_wronskian_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hZ i hi]

end DkMath.Lib.Algebra.FiniteProductWronskian
