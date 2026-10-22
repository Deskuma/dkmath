/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath

#print "file: RootSmokeNOTE031NodalReduction"

/-! 通常入口から同じ中心の方向・剰余分離・深さの同値・実際の残余点の固定へ到達する。 -/
open DkMath.Lib.NumberTheory ValuationInertia EllipticCriticalCentre EllipticTangentDirections

#check TangentDirections
#check exists_tangentDirections
#check TangentDirections.residue_ne
#check TangentDirections.inertia_fixed
#check EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model
#check DkMath.FLT.Frey.Source.exists_criticalCentre_directions_at_bad_prime
#check DkMath.FLT.Frey.Source.residual_fixed_of_not_close_to_centre
#print axioms DkMath.FLT.Frey.Source.residual_fixed_of_not_close_to_centre

/-- 同じSource 37の有限残余点を、同じ中心からの距離でC1の慣性固定へ渡す。 -/
theorem source37_nonclose (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (P : S.ResidualSpace) (hP : P.val = .some x y h) (hdepth : ¬ A.valuation (x - C.x) < 1) :
    S.residualRepresentation σ P = P := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact S.residual_fixed_of_not_close_to_centre (by decide) (by decide) A hA C σ hσ h P hP hdepth
