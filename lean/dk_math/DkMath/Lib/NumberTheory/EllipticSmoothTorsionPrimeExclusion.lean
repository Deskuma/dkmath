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

end DkMath.Lib.NumberTheory.EllipticSmoothTorsionPrimeExclusion
