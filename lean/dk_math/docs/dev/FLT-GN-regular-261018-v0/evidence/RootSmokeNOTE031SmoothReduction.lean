/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath

#print "file: RootSmokeNOTE031SmoothReduction"

/-! 通常ルートから031-002C1の局所幾何・実際の慣性固定・同じSourceへ到達する。 -/
open DkMath.Lib.NumberTheory
open EllipticGoodReductionSeparation ValuationInertia

#check SmoothCoordinates
#check HasSmoothReduction
#check EllipticGoodReductionInertia.torsion_eq_of_coordinate_congruence_of_smooth
#check EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction
#print axioms DkMath.FLT.Frey.Source.residual_fixed_of_smooth_reduction

/-- 同じSource 37の同じモデルと残余点を保つ、通常入口のスモーク。 -/
theorem source37_smooth_inertia (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : S.ResidualSpace) (hs : HasSmoothReduction (S.valuationModel A) P.val) :
    S.residualRepresentation σ P = P := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact S.residual_fixed_of_smooth_reduction (by decide) (by decide) A hA σ hσ P hs
