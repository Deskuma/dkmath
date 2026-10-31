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
The quotient class of a `q`-torsion element outside `H` has exact additive
order `q`.  This is stronger than divisibility of `Nat.card (G ⧸ H)` and does
not require the quotient to be finite: the canonical quotient map preserves
the `q`-multiple, while its kernel is exactly `H`.
-/
theorem quotient_addOrder_eq_prime_of_nsmul_not_mem
    (H : AddSubgroup G) {q : ℕ} [Fact q.Prime] (R : G)
    (hRq : q • R = 0) (hR : R ∉ H) :
    addOrderOf (QuotientAddGroup.mk' H R) = q := by
  apply addOrderOf_eq_prime
  · rw [← map_nsmul, hRq, map_zero]
  · intro hzero
    apply hR
    rw [← AddMonoidHom.mem_ker] at hzero
    simpa only [QuotientAddGroup.ker_mk'] using hzero

/-- [DkMath.Lib]
If a finite additive target is reached by a homomorphism whose kernel is `H`,
then a `q`-torsion source point outside `H` forces `q` to divide the target's
cardinality.  This is the abstract component-map interface: the later
elliptic-curve development supplies a finite component group and proves the
kernel identity, while this theorem supplies the entire group-theoretic
transport.  No Néron model, reduction map, or local-field hypothesis is used.
-/
theorem prime_dvd_finite_component_of_ker
    {G F : Type*} [AddCommGroup G] [AddCommGroup F] [Finite F]
    (H : AddSubgroup G) (φ : G →+ F) (hker : φ.ker = H)
    {q : ℕ} [Fact q.Prime] (R : G)
    (hRq : q • R = 0) (hRnot : R ∉ H) :
    q ∣ Nat.card F := by
  apply prime_dvd_natCard_of_addMonoidHom_map_nsmul_eq_zero_of_map_ne_zero φ R hRq
  intro hzero
  apply hRnot
  rw [← AddMonoidHom.mem_ker] at hzero
  rw [hker] at hzero
  exact hzero

/-- [DkMath.Lib]
An element of exact additive order `2*q` forces `q`-torsion in the quotient
unless its double is already in the subgroup.  If the subgroup has no
nonzero `q`-torsion, the latter alternative is impossible and the prime must
divide the quotient cardinality.

This is the small group-theoretic closure used by the Frey component argument:
the geometric part only has to prove that a smooth `q`-torsion point is zero.
-/
theorem prime_dvd_natCard_quotient_of_two_p_torsion
    (H : AddSubgroup G) {q : ℕ} [Fact q.Prime] (R : G)
    (horder : addOrderOf R = 2 * q)
    (hker : ∀ x : G, x ∈ H → q • x = 0 → x = 0) :
    q ∣ Nat.card (G ⧸ H) := by
  have htwoq : (2 * q) • R = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero R
  apply prime_dvd_natCard_quotient_of_nsmul_not_mem H (2 • R)
    ((mul_nsmul R 2 q).symm.trans htwoq)
  intro hdouble
  have hpdouble : q • (2 • R) = 0 := by
    exact (mul_nsmul R 2 q).symm.trans htwoq
  have hzero : 2 • R = 0 := hker (2 • R) hdouble hpdouble
  have hdiv : 2 * q ∣ 2 := by
    rw [← horder]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
  have hle : 2 * q ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hqge : 2 ≤ q := (Fact.out : q.Prime).two_le
  omega

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
