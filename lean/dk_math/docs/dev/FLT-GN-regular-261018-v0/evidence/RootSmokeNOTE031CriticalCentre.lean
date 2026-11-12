/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath

#print "file: RootSmokeNOTE031CriticalCentre"

/-! 通常入口から臨界中心の構成・剰余特異性・慣性固定・同じSourceの深さへ到達する。 -/
open DkMath.Lib.NumberTheory ValuationInertia EllipticCriticalCentre EllipticCriticalCentreAlgebra

#check translated_defect_factor
#check exists_criticalCentre
#check CriticalCentre.residue_singular_of_model
#check CriticalCentre.inertia_fixed
#check DkMath.FLT.Frey.Source.exists_criticalCentre_at_bad_prime
#print axioms DkMath.FLT.Frey.Source.exists_criticalCentre_at_bad_prime

/-- 同じSource 37の同じ中心で、座標の慣性固定とずれの37乗の深さを保つ。 -/
theorem source37_criticalCentre (S : DkMath.FLT.Frey.Source 37) (hd : (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      (∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)), σ ∈ inertiaSubgroupIn A ℚ →
        σ C.x = C.x ∧ σ C.y = C.y) ∧
      A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) =
        (A.valuation (3 : AlgebraicClosure ℚ) ^ (2 * padicValInt 3 (S.a * S.b * S.c))) ^ 37 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact S.exists_criticalCentre_at_bad_prime (by decide) (by decide) hd A hA
