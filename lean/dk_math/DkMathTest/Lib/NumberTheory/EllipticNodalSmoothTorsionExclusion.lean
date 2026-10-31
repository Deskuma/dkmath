/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion
import Lean.Util.CollectAxioms

#print "file: DkMathTest.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion"

/-!
# 回帰入口：節点の点数上界から滑らかな `2p` 捩れを排除する

このテストは、剰余曲線の有理特異中心と剰余体の濃度上界を明示入力に残す。
乗法的還元から中心を構成した、または零成分外の捩れを排除したという主張はしない。
-/

namespace DkMathTest.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion

open WeierstrassCurve IsLocalRing
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open DkMath.Lib.NumberTheory.EllipticNodalSmoothCard
open DkMath.Lib.NumberTheory.EllipticNodalSmoothCentre
open DkMath.Lib.NumberTheory.EllipticCriticalCentre
open DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]
  {A : ValuationSubring L} (W : WeierstrassCurve A)

example [Fintype (ResidueField A)] (C : CriticalCentre A (W.map A.subtype)) :
    Nat.card (W.map (residue A)).toAffine.Point ≤ Fintype.card (ResidueField A) + 1 :=
  natCard_points_le_card_add_one_of_criticalCentre W C

example {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fintype (ResidueField A)]
    (hp5 : 5 ≤ p) (hunit : A.valuation (p : L) = 1)
    (hresidueCard : Fintype.card (ResidueField A) ≤ q) (hqp : q < p)
    (C : SingularCentre (W.map (residue A)))
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p :=
  not_addOrder_eq_two_mul_prime_of_smooth_of_nodal_card_bound W hp5 hunit
    hresidueCard hqp C hQ

example {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fintype (ResidueField A)]
    (hp5 : 5 ≤ p) (hunit : A.valuation (p : L) = 1)
    (hresidueCard : Fintype.card (ResidueField A) ≤ q) (hqp : q < p)
    (C : CriticalCentre A (W.map A.subtype))
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p :=
  not_addOrder_eq_two_mul_prime_of_smooth_of_criticalCentre_card_bound W hp5 hunit
    hresidueCard hqp C hQ

#print axioms add_one_lt_of_prime_lt_of_five_le
#print axioms singularCentreOfCriticalCentre
#print axioms natCard_points_le_card_add_one_of_criticalCentre
#print axioms not_addOrder_eq_two_mul_prime_of_smooth_of_nodal_card_bound
#print axioms not_addOrder_eq_two_mul_prime_of_smooth_of_criticalCentre_card_bound

end DkMathTest.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion
