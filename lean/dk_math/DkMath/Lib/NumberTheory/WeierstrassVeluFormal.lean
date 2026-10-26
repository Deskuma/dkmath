/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from the formal-neighbourhood estimate, blob
ab1aee61bdcfbe439dcf9693d5f1417cacc05b6b, in
P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean.
Modified: arbitrary fields, valuation-ring models and finite indexed kernels.
-/

import DkMath.Lib.NumberTheory.WeierstrassVeluPair
import Mathlib.RingTheory.Valuation.ValuationSubring

#print "file: DkMath.Lib.NumberTheory.WeierstrassVeluFormal"

/-!
# 無限遠近傍では、有限核の補正は小さい

[DkMath.Lib] 整な核座標a,bと非整なxについて、v(x−a)=v(x)>1。
Vélu補正t/(x−a)+u/(x−a)²の各項は付値1未満なので、有限和も同じである。
従って商のx座標の付値は元のxの付値と正確に一致する。
節点・良還元・剰余標数の制限は不要で、2上も含む。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassVeluFormal
open WeierstrassCurve WeierstrassVeluPolynomial WeierstrassVeluPair
open scoped BigOperators
variable {F ι : Type*} [Field F] (A : ValuationSubring F) (W : WeierstrassCurve A)

/-- [DkMath.Lib] 整な代表座標によるx補正の有限和は、非整なxでは厳密に小さい。 -/
theorem correction_sum_small (s : Finset ι) (a b : ι → A) {x : F}
    (hx : 1 < A.valuation x) :
    A.valuation (∑ i ∈ s, xCorrection (W.map A.subtype) (a i) (b i) x) < 1 := by
  refine A.valuation.map_sum_lt one_ne_zero (fun i hi => ?_)
  have hd : A.valuation (x - a i) = A.valuation x :=
    Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt (A.valuation_le_one (a i)) hx)
  have ht : A.valuation (momentT (W.map A.subtype) (a i)) ≤ 1 := by
    have he : momentT (W.map A.subtype) (a i) = ((momentT W (a i) : A) : F) := rfl
    rw [he]
    exact A.valuation_le_one _
  have hu : A.valuation ((2 * (b i : F) + (W.map A.subtype).a₁ * a i +
      (W.map A.subtype).a₃) ^ 2) ≤ 1 := by
    have he : (2 * (b i : F) + (W.map A.subtype).a₁ * a i +
        (W.map A.subtype).a₃) ^ 2 = (((2 * b i + W.a₁ * a i + W.a₃) ^ 2 : A) : F) := rfl
    rw [he]
    exact A.valuation_le_one _
  apply A.valuation.map_add_lt
  · rw [map_div₀, hd, div_lt_one₀ (lt_trans zero_lt_one hx)]
    exact ht.trans_lt hx
  · simp only [map_div₀, map_pow, hd]
    rw [div_lt_one₀ (pow_pos (lt_trans zero_lt_one hx) 2)]
    simpa only [map_pow] using hu.trans_lt (one_lt_pow' hx two_ne_zero)

/-- [DkMath.Lib] 同じ補正を加えてもxの付値は変わらない。零/非零だけの比較ではない。 -/
theorem x_value_eq (s : Finset ι) (a b : ι → A) {x : F} (hx : 1 < A.valuation x) :
    A.valuation (x + ∑ i ∈ s, xCorrection (W.map A.subtype) (a i) (b i) x) = A.valuation x :=
  Valuation.map_add_eq_of_lt_left _ ((correction_sum_small A W s a b hx).trans hx)

end DkMath.Lib.NumberTheory.WeierstrassVeluFormal
