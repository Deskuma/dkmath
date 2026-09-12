/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.CosmicFormula.Projection.WorldModulus

#print "file: DkMathTest.CosmicFormula.ProjectionWorldModulus"

namespace DkMathTest.CosmicFormula.ProjectionWorldModulus

open DkMath.CosmicFormula.Projection
open DkMath.NumberTheory
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

private theorem knownPrimeScales_235 :
    KnownPrimeScales ({2, 3, 5} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num

private theorem prime_7 : Nat.Prime 7 := by norm_num

example :
    U ((primeWorldModulus ({2, 3, 5} : Finset ℕ) : ℝ) - 1) =
      1 / (primeWorldModulus ({2, 3, 5} : Finset ℕ) : ℝ) := by
  exact worldModulus_projection_gap knownPrimeScales_235

example :
    Pi ((primeWorldModulus ({2, 3, 5} : Finset ℕ) : ℝ) - 1) + 1 =
      1 / (primeWorldModulus ({2, 3, 5} : Finset ℕ) : ℝ) := by
  exact worldModulus_projection_add_one knownPrimeScales_235

example :
    1 / (primeWorldModulus (insert 7 ({2, 3, 5} : Finset ℕ)) : ℝ) =
      (1 / (primeWorldModulus ({2, 3, 5} : Finset ℕ) : ℝ)) / (7 : ℝ) := by
  exact freshPrime_refinement_mesh knownPrimeScales_235 prime_7 (by simp)

#print axioms worldModulus_projection_gap
#print axioms worldModulus_projection_add_one
#print axioms freshPrime_refinement_mesh

end DkMathTest.CosmicFormula.ProjectionWorldModulus
