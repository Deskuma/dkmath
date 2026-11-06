/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateResonantWitness

#print "file: DkMathTest.FLT.FreyTateResonantWitness"

namespace FreyTateQuotientTest
-- Local algebra regression: narrow p-preimage absorption does not imply full absorption.
private def act (x : ZMod 25 × ZMod 25) : ZMod 25 × ZMod 25 := (x.1, 6 * x.2)

example (x : ZMod 25 × ZMod 25) (h : (5 • x).2 = 0) : (act x - x).2 = 0 := by
  have hx : (5 : ZMod 25) * x.2 = 0 := by simpa using h
  change 6 * x.2 - x.2 = 0
  linear_combination hx

example : (act (0, 1) - (0, 1)).2 ≠ 0 := by decide
example : ((6 : ZMod 25).val : ZMod 5) = 1 ∧ (6 : ZMod 25) ≠ 1 := by decide
end FreyTateQuotientTest

-- Kernel axiom reports for the selected actual arithmetic endpoints.
#print axioms DkMath.FLT.Frey.Source.residualFiniteSecond
#print axioms DkMath.FLT.Frey.Source.residualFiniteSecond_surjective
#print axioms DkMath.FLT.Frey.Source.residualFiniteBasis_first
#print axioms DkMath.FLT.Frey.Source.residualFiniteSecond_eq_zero_iff
#print axioms DkMath.FLT.Frey.Source.residualFiniteQuotientEquiv
#print axioms DkMath.FLT.Frey.Source.residualFiniteSecond_action
#print axioms DkMath.FLT.Frey.Source.residualFinite_absorption_iff
#print axioms DkMath.FLT.Frey.Source.residualFinite_inertia_absorption_iff
#print axioms DkMath.FLT.Frey.Source.residualSecond_frobenius_bound
#print axioms DkMath.FLT.Frey.Source.residualSecond_frobenius_ne_one_at
#print axioms DkMath.FLT.Frey.Source.residualSecond_frobenius_ne_one
#print axioms DkMath.FLT.Frey.Source.residual_resonant_high_absorption_failure
#print axioms DkMath.FLT.Frey.Source.residual_resonant_second_witness
#print axioms DkMath.FLT.Frey.Source.residualSecond_nontrivial_resonant_inertia
