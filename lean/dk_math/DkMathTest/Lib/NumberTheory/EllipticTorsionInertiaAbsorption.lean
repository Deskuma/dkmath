/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionInertiaAbsorption

namespace DkMathTest.Lib.NumberTheory.EllipticTorsionInertiaAbsorption

open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia

-- y²=x³-x has discriminant 64, hence good reduction at 3.  At every
-- extension valuation above 3, actual inertia fixes every geometric 2-torsion
-- point.  No finite-residue or global-fixedness input is supplied.
def curve : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 0⟩

example (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    (y : Points (curve.map (Int.castRingHom ℚ))) (hy : 2 • y = 0) :
    pointAction (curve.map (Int.castRingHom ℚ)) τ y = y := by
  apply pointAction_eq_of_inertia_of_integer_good _ curve rfl Nat.prime_three
    (by decide : ¬ 3 ∣ 2) ?_ A hA τ hτ hy
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

#print axioms pointAction_sub_mem_of_inertia_absorbs
#print axioms pointAction_eq_of_inertia_of_integer_good
#print axioms pointAction_sub_mem_of_inertia_absorbs_bad_support

end DkMathTest.Lib.NumberTheory.EllipticTorsionInertiaAbsorption
