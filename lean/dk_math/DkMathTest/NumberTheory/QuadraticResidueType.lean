/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneResidueType

#print "file: DkMathTest.NumberTheory.QuadraticResidueType"

open DkMath.Lib.NumberTheory.QuadraticResidueType
open DkMath.NumberTheory.TraceOneResidueType

example : Split (-2 : ZMod 2) 1 := by simpa using split_of_even (-2) (by decide)
example : Inert (-1 : ZMod 2) 1 := by simpa using inert_of_odd (-1) (by decide)
example : Ramified (-1 : ZMod 2) 0 := gaussian_mod_two_ramified
example : Split (0 : ZMod 3) 1 := ⟨0, 1, by decide, by decide, by decide⟩
example : Inert (1 : ZMod 3) 1 := by
  intro ⟨r, hr⟩
  fin_cases r <;> revert hr <;> decide
example : Ramified (-1 : ZMod 3) 1 := by
  refine ⟨2, by decide, ?_⟩
  intro r hr
  fin_cases r
  · have hn : ¬ (0 : ZMod 3) ^ 2 = -1 + 1 * 0 := by decide
    exact False.elim (hn hr)
  · have hn : ¬ (1 : ZMod 3) ^ 2 = -1 + 1 * 1 := by decide
    exact False.elim (hn hr)
  · rfl

#print axioms split_iff_discr
#print axioms inert_iff_isField
#print axioms ramified_iff_discr
#print axioms classification
#print axioms exclusive
#print axioms gaussian_mod_two_nilpotent
#print axioms residueMap
#print axioms mod_two_dichotomy
#print axioms odd_prime_classification

#print axioms traceOne_mod_two_isField
#print axioms residueMap_surjective
