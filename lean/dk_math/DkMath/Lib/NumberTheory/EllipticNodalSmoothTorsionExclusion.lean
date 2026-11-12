/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticNodalSmoothCentre
import DkMath.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion

#print "file: DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion"

/-!
# From a rational node to exclusion of smooth `2p`-torsion

The preceding nodal-slope construction supplies
`#E_sm(k) ≤ #k + 1`.  For prime addresses `q < p` and `p ≥ 5`, elementary
arithmetic improves this to `#E_sm(𝔽_q) < p`.  As the smooth point group is
nonempty, its cardinality is not divisible by `p`; reduction injectivity then
excludes a smooth point of exact order `2*p` in the generic fiber.

The only geometric input retained here is a *rational* singular centre on the
reduced cubic.  This module does not construct that centre from multiplicative
reduction, and it does not rule out `2*p`-torsion living outside the zero
component.
-/

namespace DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion

open WeierstrassCurve IsLocalRing
open EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticNodalSmoothCard
open EllipticNodalSmoothCentre EllipticCriticalCentre
open EllipticSmoothTorsionPrimeExclusion

/-- A positive number strictly below a prime is not divisible by that prime. -/
theorem prime_not_dvd_of_pos_of_lt {p n : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hnp : n < p) : ¬ p ∣ n := by
  intro hdiv
  have hle : p ≤ n := Nat.le_of_dvd hn hdiv
  omega

/-- If `q < p` are prime and `p ≥ 5`, then already `q + 1 < p`.  The excluded
equality would force the even prime `q = 2` and hence `p = 3`. -/
theorem add_one_lt_of_prime_lt_of_five_le {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp5 : 5 ≤ p) (hqp : q < p) : q + 1 < p := by
  by_contra hlt
  have hle : p ≤ q + 1 := Nat.le_of_not_gt hlt
  have heq : p = q + 1 := by omega
  rcases (Fact.out : q.Prime).eq_two_or_odd with hq | hq
  · omega
  · have hpeven : Even p := by
      rw [heq, Nat.even_iff]
      omega
    have hptwo : p = 2 := (Fact.out : p.Prime).even_iff.mp hpeven
    omega

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]
  {A : ValuationSubring L} (W : WeierstrassCurve A)

/--
At a prime residue address below `p`, a rational node on the reduced cubic
excludes smooth points of exact order `2*p` in the generic fiber.

The proof is the complete short chain

`rational node → #E_sm ≤ q+1 < p → p ∤ #E_sm → reduction kills p-torsion`.

It intentionally concludes only that such a point cannot lie in the smooth
zero component represented by `HasSmoothReduction`.
-/
theorem not_addOrder_eq_two_mul_prime_of_smooth_of_nodal_card_bound
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fintype (ResidueField A)] (hp5 : 5 ≤ p)
    (hunit : A.valuation (p : L) = 1) (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp : q < p) (C : SingularCentre (W.map (residue A)))
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p := by
  let _ : Finite ((W.map (residue A)).toAffine.Point) := finitePoints C
  have hpos : 0 < Nat.card ((W.map (residue A)).toAffine.Point) :=
    natCard_points_pos C
  have hbound : Nat.card ((W.map (residue A)).toAffine.Point) ≤
      Fintype.card (ResidueField A) + 1 := natCard_points_le_card_add_one C
  have hlt : Nat.card ((W.map (residue A)).toAffine.Point) < p := by
    calc
      Nat.card ((W.map (residue A)).toAffine.Point) ≤ Fintype.card (ResidueField A) + 1 := hbound
      _ ≤ q + 1 := Nat.add_le_add_right hresidueCard 1
      _ < p := add_one_lt_of_prime_lt_of_five_le hp5 hqp
  exact not_addOrder_eq_two_mul_prime_of_smooth_of_residue_not_dvd_natCard W hunit
    (prime_not_dvd_of_pos_of_lt hpos hlt) hQ

/--
The preceding zero-component exclusion in the form naturally supplied by the
existing valuation-theoretic nodal API.  A `CriticalCentre` reduces to the
rational singular centre required for the slope bound, so no separate choice
of a residue point or of tangent directions is needed here.

As above, this does not construct the critical centre from a reduction-type
assumption and does not address points outside `HasSmoothReduction`.
-/
theorem not_addOrder_eq_two_mul_prime_of_smooth_of_criticalCentre_card_bound
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fintype (ResidueField A)] (hp5 : 5 ≤ p)
    (hunit : A.valuation (p : L) = 1) (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp : q < p) (C : CriticalCentre A (W.map A.subtype))
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p :=
  not_addOrder_eq_two_mul_prime_of_smooth_of_nodal_card_bound W hp5 hunit hresidueCard hqp
    (singularCentreOfCriticalCentre W C) hQ

end DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion
