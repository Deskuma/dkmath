/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.ValuationPolynomial
import DkMath.Lib.NumberTheory.EllipticDivisionMultiplication
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.RingTheory.Valuation.LocalSubring

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality"

/-!
# NOTE-031-002A: 剰余標数と互いに素なtorsionの座標は付値環に入る

標数0の整モデルWと同じ体上の曲線Eについて、nの付値が1ならΨSqₙの最高係数n²も単元となる。
実際のn-torsion点のx座標はΨSqₙの根なので、最高次項の支配から極を持たない。
y座標はxとモデルの係数によるモニック二次式の根であり、付値環の整閉性で環に入る。

良還元も乗法的還元も仮定しない。ここで得るのは座標の整性であって、
剰余曲線の非特異性や還元写像の単射性、慣性作用の自明性ではない。
モデルの基底変換等式を明示し、実際の点を別の曲線の点へ選び直さない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality
open Polynomial WeierstrassCurve
open DkMath.Lib.Algebra.ValuationPolynomial
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A) (E : WeierstrassCurve K) (hmodel : W.map A.subtype = E)
include W hmodel

/-- 実際の非無限遠n-torsion点のx座標は付値環Aへ入る。
nの単元付値は、除法多項式の最高係数を単元にするために使う。 -/
theorem torsion_x_mem {n : ℕ} (hn : A.valuation (n : K) = 1) {x y : K}
    (h : E.toAffine.Nonsingular x y) (hkill : n • (Affine.Point.some x y h) = 0) : x ∈ A := by
  classical
  have hn0 : (n : K) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hn
    exact zero_ne_one hn
  have hz : (n : ℤ) • (Affine.Point.some x y h) = 0 := by
    rw [natCast_zsmul]
    exact hkill
  have hψ := (EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ E h (n : ℤ)).mp hz
  have hsq := EllipticDivision.WeierstrassCurve.evalEval_ψ_sq E h.1 (n : ℤ)
  have hroot : (E.ΨSq (n : ℤ)).eval x = 0 := by
    rw [← hsq, hψ, zero_pow two_ne_zero]
  have hc : ∀ i, A.valuation ((E.ΨSq (n : ℤ)).coeff i) ≤ 1 := by
    intro i
    rw [← hmodel, map_ΨSq, coeff_map]
    exact (A.valuation_le_one_iff _).mpr ((W.ΨSq (n : ℤ)).coeff i).2
  have hl : A.valuation (E.ΨSq (n : ℤ)).leadingCoeff = 1 := by
    rw [E.leadingCoeff_ΨSq (by exact_mod_cast hn0)]
    push_cast
    rw [map_pow, hn, one_pow]
  exact (A.valuation_le_one_iff _).mp (valuation_root_le_one A.valuation hc hl hroot)

omit [CharZero K] [DecidableEq K] in
/-- 整モデルの方程式でxがAに入るなら、yもAに入る。
yをモニック二次式の根として扱うので、2が単元であることは要求しない。 -/
theorem y_mem_of_x_mem {x y : K} (heq : E.toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  let xa : A := ⟨x, hx⟩
  let c : A := W.a₁ * xa + W.a₃
  let d : A := -(xa ^ 3 + W.a₂ * xa ^ 2 + W.a₄ * xa + W.a₆)
  have hyint : IsIntegral A y := by
    refine ⟨X ^ 2 + C c * X + C d, by monicity!, ?_⟩
    simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
    have he := (E.toAffine.equation_iff x y).mp heq
    rw [← hmodel] at he
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.subtype_apply] at he
    simp only [c, d, map_add, map_mul, map_neg, map_pow]
    simp only [ValuationSubring.algebraMap_apply]
    dsimp [xa]
    linear_combination he
  obtain ⟨ya, hya⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).mp hyint
  rw [← hya]
  exact ya.2

/-- nの付値が1である実際のn-torsion点は、両方の有限座標が同じ付値環に入る。 -/
theorem torsion_coordinates_mem {n : ℕ} (hn : A.valuation (n : K) = 1) {x y : K}
    (h : E.toAffine.Nonsingular x y) (hkill : n • (Affine.Point.some x y h) = 0) :
    x ∈ A ∧ y ∈ A := by
  have hx := torsion_x_mem A W E hmodel hn h hkill
  exact ⟨hx, y_mem_of_x_mem A W E hmodel h.1 hx⟩

end DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality
