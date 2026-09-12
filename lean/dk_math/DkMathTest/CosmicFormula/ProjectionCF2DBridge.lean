/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.CosmicFormula.Projection.CF2DBridge

#print "file: DkMathTest.CosmicFormula.ProjectionCF2DBridge"

namespace DkMathTest.CosmicFormula.ProjectionCF2DBridge

open DkMath.CosmicFormula.Projection
open DkMath.CosmicFormula.Rotation.CF2D

example : Pi 2 + 1 = U 2 := by
  exact cosmicProjection_gap_eq 2 (by norm_num)

example : Pi (Pi 2) = 2 := by
  exact cosmicProjection_inverse 2 (by norm_num)

example {P Q : ℝ} (hP : P + 1 ≠ 0) (hQ : Q + 1 ≠ 0)
    (h : Pi P = Pi Q) : P = Q := by
  exact cosmicProjection_injective hP hQ h

example : U ((5 : ℝ) - 1) = regularPhaseStep 5 := by
  exact projectionGap_eq_regularPhaseStep (by norm_num)

example : Pi ((5 : ℝ) - 1) + 1 = regularPhaseStep 5 := by
  exact projection_add_one_eq_regularPhaseStep (by norm_num)

#print axioms cosmicProjection_gap_eq
#print axioms cosmicProjection_inverse
#print axioms cosmicProjection_injective
#print axioms projectionGap_eq_regularPhaseStep
#print axioms projection_add_one_eq_regularPhaseStep

end DkMathTest.CosmicFormula.ProjectionCF2DBridge
