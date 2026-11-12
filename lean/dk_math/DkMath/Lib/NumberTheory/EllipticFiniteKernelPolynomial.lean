/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelGeneration
import DkMath.Lib.Algebra.ValuationRationalPolynomial

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelPolynomial"

/-!
# 固定体の有理式から多項式へ

[DkMath.Lib] 定数でない楕円有理関数は各有限値を取る。
零点がないと逆関数が全点正則となって定数になるためである。
同じX_Hの有限値の点はHの外にあり、そこでは二関数とも正則。
この事実でk(X_H)の正則関数から非定数分母を除く。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation
open DkMath.Lib.Algebra
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelPolynomial :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 超越的な同じ関数fは、任意の有限値cで正の位数の零点を持つ。
値域の全射性を新たな幾何学providerにせず、全点正則なら定数という判定から示す。 -/
theorem exists_point_zero_of_transcendental
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : Transcendental (AlgebraicClosure K) f) (c : AlgebraicClosure K) :
    ∃ P : Points E, pointValuation E P (f - algebraMap _ _ c) < 1 := by
  by_contra! hno
  obtain ⟨b, hb⟩ := eq_const_of_pointValuation_le_one E (f - algebraMap _ _ c)⁻¹ (fun P => by
    rw [map_inv₀]
    exact (inv_le_one₀ (zero_lt_one.trans_le (hno P))).mpr (hno P))
  have hi : IsAlgebraic (AlgebraicClosure K) ((f - algebraMap _ _ c)⁻¹) := by
    rw [hb]
    exact isAlgebraic_algebraMap b
  have hsub : IsAlgebraic (AlgebraicClosure K) (f - algebraMap _ _ c) := IsAlgebraic.inv_iff.mp hi
  apply hf
  simpa only [sub_add_cancel] using hsub.add (isAlgebraic_algebraMap c)

/-- [DkMath.Lib] 同じX_Hの有限値の零点は、極支持Hの外で検出できる。 -/
theorem exists_veluX_finite_value (H : AddSubgroup (Points E)) [Fintype H]
    (c : AlgebraicClosure K) :
    ∃ P : Points E, P ∉ H ∧ pointValuation E P (veluX E H - algebraMap _ _ c) < 1 := by
  obtain ⟨P, hP⟩ := exists_point_zero_of_transcendental E _ (veluX_transcendental E H) c
  refine ⟨P, ?_, hP⟩
  intro hmem
  have hx : 1 < pointValuation E P (veluX E H) := by
    rw [veluX_valuation_of_mem E H P hmem, ← exp_zero, exp_lt_exp]; norm_num
  have he := (pointValuation E P).map_sub_eq_of_lt_left
    ((pointValuation_const_le_one E P c).trans_lt hx)
  rw [he] at hP
  exact (lt_asymm hx hP)

/-- [DkMath.Lib] 同じX_Hの単純体の元がHの外で正則なら、X_Hの多項式である。
同じ関数の有限値を用い、生成元を新しく選び直さない。 -/
theorem exists_polynomial_of_kernel_regular (H : AddSubgroup (Points E)) [Fintype H]
    (g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hg : g ∈ (AlgebraicClosure K)⟮veluX E H⟯)
    (hreg : ∀ P : Points E, P ∉ H → pointValuation E P g ≤ 1) :
    ∃ p : (AlgebraicClosure K)[X], g = aeval (veluX E H) p := by
  apply ValuationRationalPolynomial.exists_polynomial_of_regular
    (fun P : {P : Points E // P ∉ H} => pointValuation E P.val)
    (fun P c => pointValuation_const_le_one E P.val c) _ (veluX_transcendental E H) ?_ hg
    (fun P => hreg P.val P.property)
  intro c
  obtain ⟨P, hP, hc⟩ := exists_veluX_finite_value E H c
  exact ⟨⟨P, hP⟩, veluX_regular_outside E H P hP, hc⟩

/-- [DkMath.Lib] 多項式になった同じ関数のOでの極上界が、多項式次数の上界を与える。
零多項式のnatDegree=0を別扱いし、最高項の公式は非零多項式にだけ適用する。 -/
theorem polynomial_natDegree_le_of_pole_bound (H : AddSubgroup (Points E)) [Fintype H]
    (p : (AlgebraicClosure K)[X]) (n : ℕ)
    (hp : pointValuation E (0 : Points E) (aeval (veluX E H) p) ≤ exp (n : ℤ)) :
    2 * p.natDegree ≤ n := by
  by_cases h0 : p = 0
  · simp [h0]
  have hx : 1 < pointValuation E (0 : Points E) (veluX E H) := by
    change 1 < pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point) (veluX E H)
    rw [veluX_valuation_zero, ← exp_zero, exp_lt_exp]; norm_num
  have hv := (pointValuation E (0 : Points E)).map_aeval_eq_pow_of_one_lt
    (fun c hc => pointValuation_const_eq_one E (0 : Points E) hc) hx h0
  rw [hv] at hp
  change pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point) (veluX E H) ^ p.natDegree ≤ _ at hp
  rw [veluX_valuation_zero, ← exp_nsmul, nsmul_eq_mul, exp_le_exp] at hp
  exact_mod_cast (by omega : (2 : ℤ) * p.natDegree ≤ n)

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
