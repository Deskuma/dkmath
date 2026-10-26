/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.DedekindLocalParameter
import DkMath.Lib.NumberTheory.EllipticWeilTransport

#print "file: DkMath.Lib.NumberTheory.EllipticFinitePointApproximation"

/-!
# 有限点集合の一点だけに一次の零点を置く

[DkMath.Lib] 前回のDedekind環のCRTを、同じ楕円曲線の任意の有限点集合へ接続する。
全ての指定点が有限であることを保持し、一点の位数1と他の点の位数0を同時に供給する。
核や巡回性は不要で、相異なる二つのH軌道を分離する関数の構成に使える。
-/
namespace DkMath.Lib.NumberTheory.EllipticFinitePointApproximation
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation
open IsDedekindDomain.HeightOneSpectrum
attribute [local instance] geometricCoordinateRing_isDedekindDomain
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- [DkMath.Lib] 同じ曲線の有限点集合Sの一点Pのみで一次に消える関数が存在する。
Sの外の零点・極を制御する主張は含めない。 -/
theorem exists_parameter_on_finset (S : Finset (Points E))
    (hS : ∀ R ∈ S, R ≠ 0) (P : Points E) (hP : P ∈ S) :
    ∃ f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField, f ≠ 0 ∧
      pointValuation E P f = exp (-1 : ℤ) ∧
      ∀ R ∈ S, R ≠ P → pointValuation E R f = 1 := by
  classical
  let w (R : S) := placeOf E (AlgebraicClosure K) R.val (hS R.val R.property)
  have hinj : Function.Injective w := by
    intro R T he
    exact Subtype.ext (placeOf_injective E (AlgebraicClosure K)
      (hS R.val R.property) (hS T.val T.property) he)
  obtain ⟨a, ha₀, ha⟩ := DedekindLocalParameter.exists_parameter w hinj (⟨P, hP⟩ : S)
  let f := algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField a
  have hv (R : S) : pointValuation E R.val f = (w R).intValuation a := by
    have he : pointValuation E R.val f = (w R).valuation _ f := by
      unfold pointValuation
      split_ifs with hz
      · exact (hS R.val R.property hz).elim
      · rfl
    exact he.trans (valuation_of_algebraMap (w R) a)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro hz
    apply ha₀
    apply IsFractionRing.injective (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    simpa only [map_zero] using hz
  · exact (hv ⟨P, hP⟩).trans ((ha ⟨P, hP⟩).trans (ite_eq_left rfl))
  · intro R hR hRP
    exact (hv ⟨R, hR⟩).trans ((ha ⟨R, hR⟩).trans
      (ite_eq_right (fun he => hRP (congrArg Subtype.val he))))

end DkMath.Lib.NumberTheory.EllipticFinitePointApproximation
