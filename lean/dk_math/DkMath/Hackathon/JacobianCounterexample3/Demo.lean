/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge

namespace DkMath.Hackathon.JacobianCounterexample3

/-- Demo certificate: the normalized formal Jacobian determinant is one. -/
theorem jacobianDemo_det_eq_one :
    normalizedJacobianMatrixC.det =
      MvPolynomial.C (1 : ℂ) :=
  normalizedJacobianMatrixC_det_eq_one

/-- Demo certificate: three distinct points lie in one normalized fiber. -/
theorem jacobianDemo_three_point_collision :
    p0C ≠ p1C ∧ p0C ≠ p2C ∧ p1C ≠ p2C ∧
      evalNormalizedCounterexampleC p0C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p1C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p2C = normalizedTargetC :=
  normalized_three_point_collision_C

/-- Demo certificate: the normalized polynomial map is not injective. -/
theorem jacobianDemo_notInjective :
    ¬ Function.Injective evalNormalizedCounterexampleC :=
  evalNormalizedCounterexampleC_notInjective

/-- Demo certificate: the normalized map has no set-theoretic left inverse. -/
theorem jacobianDemo_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalNormalizedCounterexampleC :=
  evalNormalizedCounterexampleC_noLeftInverse

/-- Demo certificate: the common output has no unique restoring input Gap. -/
theorem jacobianDemo_target_notUniqueGap :
    ¬ DkMath.BookOfMagic.UniqueGap
      normalizedRestoreRelC
      normalizedTargetC :=
  normalizedTargetC_not_uniqueGap

/--
Presentation surface for a complex polynomial map whose formal Jacobian
determinant is one but which is not injective.
-/
theorem jacobianDemoCertificateC :
    normalizedJacobianMatrixC.det =
        MvPolynomial.C (1 : ℂ) ∧
    normalizedJacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalNormalizedCounterexampleC :=
  normalizedJacobianCounterexampleCertificateC

end DkMath.Hackathon.JacobianCounterexample3

#print "file: DkMath.Hackathon.JacobianCounterexample3.Demo"
