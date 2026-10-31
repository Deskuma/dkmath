/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticRationalLocalTransport

namespace DkMathTest.Lib.NumberTheory.EllipticRationalLocalTransport

open DkMath.Lib.NumberTheory
open EllipticRationalLocalTransport EllipticTorsionRepresentation
open EllipticGoodReductionSeparation FreyLocalReduction

-- Both small-prime addresses use the same rational point; the extension
-- residue field is neither finite nor supplied with a cardinality bound.
example (W : WeierstrassCurve ℤ)
    (P : (W.map (Int.castRingHom ℚ)).toAffine.Point)
    (A₂ A₃ : ValuationSubring (AlgebraicClosure ℚ))
    (h₂ : ValuationInertia.LiesOverPrime A₂ 2)
    (h₃ : ValuationInertia.LiesOverPrime A₃ 3)
    (hn₂ : ¬ HasSmoothReduction (W.map (Int.castRingHom (localValuationSubring 2))) P)
    (hn₃ : ¬ HasSmoothReduction (W.map (Int.castRingHom (localValuationSubring 3))) P) :
    ¬ HasSmoothReduction (W.map (Int.castRingHom A₂))
        (baseChangePoint (W.map (Int.castRingHom ℚ)) P) ∧
      ¬ HasSmoothReduction (W.map (Int.castRingHom A₃))
        (baseChangePoint (W.map (Int.castRingHom ℚ)) P) := by
  exact ⟨fun h => hn₂ ((hasSmoothReduction_localValuationSubring_baseChange_iff W A₂ h₂ P).mp h),
    fun h => hn₃ ((hasSmoothReduction_localValuationSubring_baseChange_iff W A₃ h₃ P).mp h)⟩

#print axioms ratCast_nonunits_iff
#print axioms hasSmoothReduction_integer_baseChange_iff
#print axioms hasSmoothReduction_iff_zero_or_exists
#print axioms integer_residue_invariants_iff

end DkMathTest.Lib.NumberTheory.EllipticRationalLocalTransport
