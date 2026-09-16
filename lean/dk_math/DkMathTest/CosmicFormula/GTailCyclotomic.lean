/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailCyclotomic

#print "file: DkMathTest.CosmicFormula.GTailCyclotomic"

open scoped BigOperators

namespace DkMathTest.CosmicFormula

open DkMath.CosmicFormula
open DkMath.Lib.NumberTheory

example (X : ℚ) :
    (∏ m ∈ (5 : ℕ).divisors.erase 1, cyclotomicEval m X) =
      ∑ i ∈ Finset.range 5, X ^ i := by
  exact prod_cyclotomicEval_eq_geomSum (by norm_num) X

example {p : ℕ} (hp : Nat.Prime p) (x u : ℚ) (hx : x ≠ 0) :
    GTail p 1 x u =
      GTailCyclotomicHomEval p (Polynomial.cyclotomic p ℤ) x u := by
  exact GTail_one_eq_cyclotomicHomEval_of_prime hp x u hx

example (x u : ℚ) (hx : x ≠ 0) :
    GTail 5 1 x u = GTailCyclotomicShell 5 x u := by
  exact GTail_one_eq_GTailCyclotomicShell_of_ne_zero x u hx

end DkMathTest.CosmicFormula
