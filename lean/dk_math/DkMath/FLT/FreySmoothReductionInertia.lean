/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyValuationArithmetic
import DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia

#print "file: DkMath.FLT.FreySmoothReductionInertia"

/-!
# NOTE-031-002C1: Freyの滑らかな還元を持つ残余点

同じFrey Source、同じ付値環モデル、同じ実際のE[p]を保つ。
q≠pならpはq上の単元である。従って一点が滑らかに還元すれば慣性に固定される。
q∣abcの悪い還元でも適用できるが、特異点へ落ちる点の固定はまだ供給しない。
その枝を埋めるには判別式付値のp可除性と零成分外の深さ・分岐の議論が必要である。
この定理のhsは明示的な剰余偏微分の条件であり、慣性固定を仮定するproviderではない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport EllipticGoodReductionSeparation
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- q≠pで滑らかに還元する同じ実際の残余点は、全てのq上の慣性元に固定される。
q≠2やq∤abcを要求しない。残るhsは一点での剰余非特異性であり、
Sourceのモデル一致・指数の単元性・座標整性・合同・単射性は実装済みの定理から供給する。 -/
theorem residual_fixed_of_smooth_reduction {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : S.ResidualSpace) (hs : HasSmoothReduction (S.valuationModel A) P.val) :
    S.residualRepresentation σ P = P := by
  have hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    apply valuation_intCast_eq_one_of_not_dvd A hq ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := (p : ℤ))
    intro h
    have hqp' : q ∣ p := by exact_mod_cast h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hqp')
  exact EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction S.rationalCurve p A
    (S.valuationModel A) (S.valuationModel_map A) hn σ hσ P hs

end DkMath.FLT.Frey.Source
