/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion
import Lean.Util.CollectAxioms

#print "file: DkMathTest.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion"

/-!
# 滑らかな素数捩れ排除の回帰入口

乗法的還元の `q - 1` / `q + 1` 濃度公式はこのテストでは仮定しない。
その代わり、剰余滑らか点群の `p` 非可除性を明示入力として、滑らかな
一般ファイバーの `p`-torsion が零に戻る公開定理を検査する。
-/

namespace DkMathTest.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion

open WeierstrassCurve IsLocalRing
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open DkMath.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]
  {A : ValuationSubring L} (W : WeierstrassCurve A)

example {p : ℕ} [Fact p.Prime] (hunit : A.valuation (p : L) = 1)
    (hcard : ¬ p ∣ Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point))
    {P : (W.map A.subtype).toAffine.Point}
    (hP : HasSmoothReduction W P) (hp : p • P = 0) : P = 0 :=
  eq_zero_of_smooth_prime_torsion_of_residue_not_dvd_natCard W hunit hcard hP hp

example {p : ℕ} [Fact p.Prime] (hunit : A.valuation (p : L) = 1)
    (hcard : ¬ p ∣ Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point))
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p :=
  not_addOrder_eq_two_mul_prime_of_smooth_of_residue_not_dvd_natCard W hunit hcard hQ

example {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hunit : A.valuation (p : L) = 1) (hqp : q < p)
    (hcard : Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point) = q - 1)
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p :=
  not_addOrder_eq_two_mul_prime_of_smooth_of_residue_card_eq_sub_one W hunit hqp hcard hQ

example {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp5 : 5 ≤ p)
    (hunit : A.valuation (p : L) = 1) (hqp : q < p)
    (hcard : Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point) = q + 1)
    {Q : (W.map A.subtype).toAffine.Point}
    (hQ : HasSmoothReduction W Q) : addOrderOf Q ≠ 2 * p :=
  not_addOrder_eq_two_mul_prime_of_smooth_of_residue_card_eq_add_one W hp5 hunit hqp hcard hQ

#print axioms eq_zero_of_smooth_prime_torsion_of_residue_not_dvd_natCard
#print axioms not_addOrder_eq_two_mul_prime_of_smooth_of_residue_not_dvd_natCard
#print axioms not_addOrder_eq_two_mul_prime_of_smooth_of_residue_card_eq_sub_one
#print axioms not_addOrder_eq_two_mul_prime_of_smooth_of_residue_card_eq_add_one

end DkMathTest.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion
