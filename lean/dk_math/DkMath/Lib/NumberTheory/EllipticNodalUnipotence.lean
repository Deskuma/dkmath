/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticNodalDecomposition
import DkMath.Lib.NumberTheory.EllipticNodalInertia
import DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia

#print "file: DkMath.Lib.NumberTheory.EllipticNodalUnipotence"

/-!
# 同じ節点モデルの有限捩れ上の慣性差分

慣性差は滑らかに還元し、単元次数の滑らかな捩れ点は慣性に固定される。
同じ作用の差分積が零になることを証明する。Tate 曲線や分類定理を入力しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticNodalUnipotence
open EllipticTorsionRepresentation EllipticCriticalCentre EllipticTangentDirections
open EllipticNodalDecomposition ValuationInertia
noncomputable section
variable (E : WeierstrassCurve ℚ) (n : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : WeierstrassCurve A)
    (hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (hn : A.valuation (n : AlgebraicClosure ℚ) = 1)

include hmodel D hn

/-- 同じ慣性群の二元について、実際の差分作用の積は零。 -/
theorem inertia_difference_product_zero
    (σ τ : Field.absoluteGaloisGroup ℚ) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (representation E n σ - 1) * (representation E n τ - 1) = 0 := by
  classical
  apply LinearMap.ext
  intro P
  let Q : Torsion E n := (representation E n τ - 1) P
  have hdec := (ValuationTameCharacter.TameCharacter.mem_inertiaSubgroupIn_iff.mp hτ).1
  have hs : EllipticGoodReductionSeparation.HasSmoothReduction M Q.val :=
    EllipticNodalInertia.inertia_difference_smooth E A M hmodel C D τ hτ
      (centre_decomposition_fixed E A C τ hdec) P.val
  have hf := EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction E n A M
    hmodel hn σ hσ Q hs
  change representation E n σ Q - Q = 0
  exact sub_eq_zero.mpr hf

/-- 同じ有限捩れ作用の慣性差分は二次冪零。 -/
theorem inertia_difference_square_zero
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (representation E n τ - 1) ^ 2 = 0 := by
  rw [pow_two]
  exact inertia_difference_product_zero E n A M hmodel C D hn τ τ hτ hτ

end
end DkMath.Lib.NumberTheory.EllipticNodalUnipotence
