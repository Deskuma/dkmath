/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteAdditiveTorsionCard
import DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction

#print "file: DkMath.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion"

/-!
# 滑らかな還元群の位数から素数捩れを排除する

付値環上の曲線の零成分では、単元位数の捩れは滑らかな剰余点群へ単射に還元する。
従って、その剰余点群の位数が素数 `p` で割れなければ、一般ファイバーの滑らかな
`p`-捩れ点は零点だけである。

このファイルは乗法的還元の滑らかな剰余点群が `q - 1` または `q + 1` 個であることを
証明しない。その正確な濃度計算は、分裂・非分裂成分群を構成する局所幾何の課題として
分離する。ここで固定するのは、その計算を受け取った後の還元単射と有限群論の接続である。
-/

namespace DkMath.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion

open WeierstrassCurve IsLocalRing EllipticGoodReductionSeparation
open EllipticSmoothReduction EllipticSmoothTorsionReduction

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]
  {A : ValuationSubring L} (W : WeierstrassCurve A)

/--
Let `p` be prime and a unit of the valuation ring.  If `p` does not divide the
cardinality of the smooth reduced point group, then every smooth `p`-torsion
point of the general fiber is zero.

The proof has two independent textbook steps.  First, reduction preserves
`p`-torsion and the cardinality hypothesis kills the reduced point.  Second,
`reduce_injOn_torsion` identifies two smooth `p`-torsion points with equal
reduction.  No claim about multiplicative reduction, component groups, or a
specific cardinality formula is made here.
-/
theorem eq_zero_of_smooth_prime_torsion_of_residue_not_dvd_natCard
    {p : ℕ} [Fact p.Prime] (hunit : A.valuation (p : L) = 1)
    (hcard : ¬ p ∣ Nat.card ((W.map (residue A)).toAffine.Point))
    {P : (W.map A.subtype).toAffine.Point}
    (hP : HasSmoothReduction W P) (hp : p • P = 0) : P = 0 := by
  classical
  have hredtorsion : p • reducePointSmooth W P = 0 :=
    nsmul_reduce_eq_zero W hP p hp
  have hredzero : reducePointSmooth W P = 0 :=
    DkMath.Lib.Algebra.eq_zero_of_nsmul_eq_zero_of_not_dvd_natCard hcard
      (reducePointSmooth W P) hredtorsion
  apply reduce_injOn_torsion W hunit ⟨hP, hp⟩
    ⟨hasSmoothReduction_zero W _, nsmul_zero _⟩
  simpa only [reducePointSmooth_zero] using hredzero

/--
Under the same residue-cardinality hypothesis, a smooth point cannot have
exact order `2 * p`.  Indeed, twice such a point is a nonzero `p`-torsion
point and remains in the smooth zero component; the preceding theorem makes
that double zero, contradicting the asserted order.

This is the direct local interface for the rational `2*p`-torsion point
produced by a Cofixed line.  It only excludes that point from the zero
component.  It does not say that the point cannot exist globally: a nonzero
component-group image remains possible and is precisely the next issue.
-/
theorem not_addOrder_eq_two_mul_prime_of_smooth_of_residue_not_dvd_natCard
    {p : ℕ} [Fact p.Prime] (hunit : A.valuation (p : L) = 1)
    (hcard : ¬ p ∣ Nat.card ((W.map (residue A)).toAffine.Point))
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p := by
  classical
  intro horder
  let Q₀ : zeroComponentSubgroup W := ⟨Q, hQ⟩
  have hdouble_smooth : HasSmoothReduction W (2 • Q) := by
    change HasSmoothReduction W (2 • Q₀).val
    exact (2 • Q₀).property
  have htwo_p : (2 * p) • Q = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero Q
  have hpdouble : p • (2 • Q) = 0 := by
    exact (mul_nsmul Q 2 p).symm.trans htwo_p
  have hdouble_zero : 2 • Q = 0 :=
    eq_zero_of_smooth_prime_torsion_of_residue_not_dvd_natCard W hunit hcard
      hdouble_smooth hpdouble
  have hdiv : 2 * p ∣ 2 := by
    rw [← horder]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hdouble_zero
  have hle : 2 * p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

/--
For distinct prime addresses below a prime exponent, the split
multiplicative cardinality `q - 1` is not divisible by `p`.

This is deliberately only an arithmetic lemma.  The geometric assertion that a
split nodal smooth special fiber has exactly `q - 1` points belongs to the
separate multiplicative-reduction construction.  Keeping the two statements
apart lets that construction discharge precisely one cardinality equality.
-/
theorem prime_not_dvd_sub_one_of_prime_lt
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hqp : q < p) :
    ¬ p ∣ q - 1 := by
  intro hdiv
  have hqpos : 0 < q - 1 := by
    have hqge : 2 ≤ q := (Fact.out : q.Prime).two_le
    omega
  have hle : p ≤ q - 1 := Nat.le_of_dvd hqpos hdiv
  omega

/--
For prime addresses `q < p` and `p ≥ 5`, the nonsplit multiplicative
cardinality `q + 1` is not divisible by `p`.

The only boundary case in which a prime can divide this positive number without
being larger is `p = q + 1`.  Then `q` would be an even prime, hence `q = 2`
and `p = 3`, which contradicts `p ≥ 5`.  This finite arithmetic is the exact
input needed once the nonsplit nodal point-count formula is supplied.
-/
theorem prime_not_dvd_add_one_of_prime_lt
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp5 : 5 ≤ p) (hqp : q < p) :
    ¬ p ∣ q + 1 := by
  intro hdiv
  have hle : p ≤ q + 1 := Nat.le_of_dvd (by omega) hdiv
  have heq : p = q + 1 := by omega
  rcases (Fact.out : q.Prime).eq_two_or_odd with hq | hq
  · omega
  · have hpeven : Even p := by
      rw [heq, Nat.even_iff]
      omega
    have hptwo : p = 2 := (Fact.out : p.Prime).even_iff.mp hpeven
    omega

/--
The split multiplicative cardinality formula closes the zero-component branch.
If a smooth reduced point group has `q - 1` elements, then a smooth point of
exact order `2 * p` cannot occur for a prime address `q < p`.

The hypothesis is written as an equality of `Nat.card`, rather than as a new
structure class for split reduction: this is the exact output expected from a
future nodal-geometry construction and keeps this theorem usable for any model
that supplies the same count.
-/
theorem not_addOrder_eq_two_mul_prime_of_smooth_of_residue_card_eq_sub_one
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hunit : A.valuation (p : L) = 1)
    (hqp : q < p) (hcard : Nat.card ((W.map (residue A)).toAffine.Point) = q - 1)
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p := by
  exact not_addOrder_eq_two_mul_prime_of_smooth_of_residue_not_dvd_natCard W hunit
    (by simpa only [hcard] using prime_not_dvd_sub_one_of_prime_lt hqp) hQ

/--
The nonsplit multiplicative cardinality formula closes the same
zero-component branch.  The lower bound `5 ≤ p` removes the exceptional
identity `3 = 2 + 1`, the only possible prime collision for `q + 1`.

As in the split case, this is a transport theorem from a concrete point-count
identity, not a proof of the identity or of nonsplit multiplicative reduction.
-/
theorem not_addOrder_eq_two_mul_prime_of_smooth_of_residue_card_eq_add_one
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp5 : 5 ≤ p)
    (hunit : A.valuation (p : L) = 1) (hqp : q < p)
    (hcard : Nat.card ((W.map (residue A)).toAffine.Point) = q + 1)
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p := by
  exact not_addOrder_eq_two_mul_prime_of_smooth_of_residue_not_dvd_natCard W hunit
    (by simpa only [hcard] using prime_not_dvd_add_one_of_prime_lt hp5 hqp) hQ

end DkMath.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion
