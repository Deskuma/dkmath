/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.Basic

#print "file: DkMathTest.CosmicFormula.ThreeElement.Basic"

namespace DkMathTest.CosmicFormula.ThreeElement.Basic

open DkMath.CosmicFormula.ThreeElement

example (x u : ℤ) :
    plusWhole x u =
      coreTerm x + interactionBeam x u + gapTerm u := by
  exact plusWhole_eq_core_add_beam_add_gap x u

example (x u : ℚ) :
    minusWhole x u =
      coreTerm x - interactionBeam x u + gapTerm u := by
  exact minusWhole_eq_core_sub_beam_add_gap x u

example (x u : ℚ) :
    plusWhole x u - minusWhole x u =
      2 * interactionBeam x u := by
  exact plusWhole_sub_minusWhole_eq_two_mul_interactionBeam x u

example (x u : ℝ) :
    plusWhole x u + minusWhole x u =
      2 * squareMass x u := by
  exact plusWhole_add_minusWhole_eq_two_mul_squareMass x u

example (x u : ℤ) :
    squareMass x u = squareMass u x := by
  exact squareMass_swap x u

example (x u : ℚ) :
    interactionBeam x u = interactionBeam u x := by
  exact interactionBeam_swap x u

example (x : ℝ) :
    coreTerm x = gapTerm x := by
  exact coreTerm_eq_gapTerm_same_input x

#print axioms DkMath.CosmicFormula.ThreeElement.plusWhole_eq_core_add_beam_add_gap
#print axioms DkMath.CosmicFormula.ThreeElement.minusWhole_eq_core_sub_beam_add_gap
#print axioms DkMath.CosmicFormula.ThreeElement.plusWhole_sub_minusWhole_eq_two_mul_interactionBeam
#print axioms DkMath.CosmicFormula.ThreeElement.plusWhole_add_minusWhole_eq_two_mul_squareMass
#print axioms DkMath.CosmicFormula.ThreeElement.squareMass_swap
#print axioms DkMath.CosmicFormula.ThreeElement.interactionBeam_swap
#print axioms DkMath.CosmicFormula.ThreeElement.coreTerm_eq_gapTerm_same_input

end DkMathTest.CosmicFormula.ThreeElement.Basic
