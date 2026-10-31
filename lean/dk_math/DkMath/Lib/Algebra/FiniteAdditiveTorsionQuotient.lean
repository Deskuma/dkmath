/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteAdditiveTorsionCard

#print "file: DkMath.Lib.Algebra.FiniteAdditiveTorsionQuotient"

/-!
# Prime torsion detected in an additive component quotient

Let `H` be a subgroup of an additive group `G`.  The quotient `G ⧸ H` is the
abstract interface of a component group: in the elliptic application, `H` is
the subgroup of points with smooth reduction.  This file deliberately does
not construct a Néron component group or assume that the quotient is finite.

The first theorem records the elementary but essential bridge:

`q • R = 0` and `R ∉ H` imply `q ∣ Nat.card (G ⧸ H)`.

For a point of order `2*q`, applying it to `2 • R` gives the exact residual
dichotomy needed after zero-component exclusion.  Either the double has
returned to the zero component, or the prime `q` occurs in the component
quotient.  The result does not claim that either alternative is impossible.
-/

namespace DkMath.Lib.Algebra

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- [DkMath.Lib]
If a `q`-torsion point is nonzero in the quotient by `H`, then `q` divides
the quotient's natural cardinality.  This is the canonical-projection
specialization of `prime_dvd_natCard_of_addMonoidHom_map_nsmul_eq_zero_of_map_ne_zero`.
-/
theorem prime_dvd_natCard_quotient_of_nsmul_not_mem
    (H : AddSubgroup G) {q : ℕ} [Fact q.Prime] (R : G)
    (hRq : q • R = 0) (hR : R ∉ H) :
    q ∣ Nat.card (G ⧸ H) := by
  apply prime_dvd_natCard_of_addMonoidHom_map_nsmul_eq_zero_of_map_ne_zero
    (QuotientAddGroup.mk' H) R hRq
  intro hzero
  apply hR
  rw [← AddMonoidHom.mem_ker] at hzero
  simpa only [QuotientAddGroup.ker_mk'] using hzero

/-- [DkMath.Lib]
For an element of exact order `2*q`, the obstruction remaining after passing
to a component quotient has only two forms.  Either its double belongs to
`H`, or `q` divides the quotient cardinality.

This is intentionally a dichotomy, not a component-group computation.  A
later local theorem may rule out one branch by geometry and the other by an
explicit component-group order calculation.
-/
theorem two_nsmul_mem_or_prime_dvd_natCard_quotient_of_addOrder_eq_two_mul_prime
    (H : AddSubgroup G) {q : ℕ} [Fact q.Prime] (R : G)
    (horder : addOrderOf R = 2 * q) :
    2 • R ∈ H ∨ q ∣ Nat.card (G ⧸ H) := by
  by_cases hdouble : 2 • R ∈ H
  · exact Or.inl hdouble
  · right
    apply prime_dvd_natCard_quotient_of_nsmul_not_mem H (2 • R) _ hdouble
    have htwoq : (2 * q) • R = 0 := by
      rw [← horder]
      exact addOrderOf_nsmul_eq_zero R
    exact (mul_nsmul R 2 q).symm.trans htwoq

end
end DkMath.Lib.Algebra
