/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteAdditiveTorsionQuotient

#print "file: DkMathTest.Lib.Algebra.FiniteAdditiveTorsionQuotient"

/-!
# Regression uses for torsion in additive quotients

These examples document the two interfaces used by a future component-group
construction: a prime-torsion class detects prime quotient cardinality, and
an exact `2*q`-torsion class has the stated double-or-component alternative.
-/

namespace DkMathTest.Lib.Algebra.FiniteAdditiveTorsionQuotient

open DkMath.Lib.Algebra

noncomputable section

variable {G : Type*} [AddCommGroup G]

example (H : AddSubgroup G) {q : ℕ} [Fact q.Prime] (R : G)
    (hRq : q • R = 0) (hR : R ∉ H) :
    q ∣ Nat.card (G ⧸ H) :=
  prime_dvd_natCard_quotient_of_nsmul_not_mem H R hRq hR

example (H : AddSubgroup G) {q : ℕ} [Fact q.Prime] (R : G)
    (horder : addOrderOf R = 2 * q) :
    2 • R ∈ H ∨ q ∣ Nat.card (G ⧸ H) :=
  two_nsmul_mem_or_prime_dvd_natCard_quotient_of_addOrder_eq_two_mul_prime H R horder

#print axioms DkMath.Lib.Algebra.prime_dvd_natCard_quotient_of_nsmul_not_mem
#print axioms DkMath.Lib.Algebra.two_nsmul_mem_or_prime_dvd_natCard_quotient_of_addOrder_eq_two_mul_prime

end
end DkMathTest.Lib.Algebra.FiniteAdditiveTorsionQuotient
