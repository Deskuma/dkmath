/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry
import DkMath.CosmicFormula.Rotation.CF2D.CycleDivision

#print "file: DkMathTest.NumberGeometry.TwoPrimePhaseAxiomAudit"

namespace DkMathTest.NumberGeometry

open DkMath.NumberGeometry.Phase

#check TwoPrimePhase
#check TwoPrimePhase.halfTurn
#check TwoPrimePhase.fullTurn
#check TwoPrimePhase.evenPhase_pow
#check TwoPrimePhase.oddPhase_pow
#check TwoPrimePhase.zeta_pow_p
#check TwoPrimePhase.evenPhase_eq_zeta_pow
#check TwoPrimePhase.oddPhase_eq_eta_mul_zeta_pow
#check TwoPrimePhase.zeta_isPrimitiveRoot
#check TwoPrimePhase.evenPhaseFin_injective
#check TwoPrimePhase.oddPhaseFin_injective
#check TwoPrimePhase.evenPhaseFin_ne_oddPhaseFin
#check TwoPrimePhase.even_signed_equation
#check TwoPrimePhase.odd_signed_equation
#check complexEta_isPrimitiveRoot
#check complexEta_pow_eq_neg_one

open DkMath.CosmicFormula.Rotation.CF2D

/-- The CF2D regular kernel has exact order `2 * p` for positive `p`. -/
theorem regularKernel_twoPrime_exactOrder {p : ℕ} (hp : 0 < p) :
    orderOf (regularKernel (2 * p)) = 2 * p := by
  exact orderOf_regularKernel (by omega)

#check regularKernel_twoPrime_exactOrder

#print axioms TwoPrimePhase.halfTurn
#print axioms TwoPrimePhase.fullTurn
#print axioms TwoPrimePhase.evenPhase_pow
#print axioms TwoPrimePhase.oddPhase_pow
#print axioms TwoPrimePhase.zeta_pow_p
#print axioms TwoPrimePhase.even_signed_equation
#print axioms TwoPrimePhase.odd_signed_equation
#print axioms TwoPrimePhase.evenPhaseFin_injective
#print axioms TwoPrimePhase.oddPhaseFin_injective
#print axioms TwoPrimePhase.evenPhaseFin_ne_oddPhaseFin
#print axioms complexEta_isPrimitiveRoot
#print axioms complexEta_pow_eq_neg_one
#print axioms regularKernel_twoPrime_exactOrder

end DkMathTest.NumberGeometry
