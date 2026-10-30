/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.Algebra.PolynomialProportional

#print "file: DkMathTest.Lib.Algebra.PolynomialProportional"

namespace DkMathTest.PolynomialProportional

open Polynomial

variable {K : Type*} [Field K]

example {F G A D : K[X]}
    (hcop : IsCoprime F G)
    (hF : F ≠ 0)
    (hA : A ≠ 0)
    (hcross : F * D = A * G)
    (hdeg : A.natDegree ≤ F.natDegree) :
    ∃ u : K, u ≠ 0 ∧ A = C u * F ∧ D = C u * G :=
  DkMath.Lib.Algebra.proportional_of_cross_relation_of_coprime
    hcop hF hA hcross hdeg

#print axioms
  DkMath.Lib.Algebra.proportional_of_cross_relation_of_coprime

end DkMathTest.PolynomialProportional
