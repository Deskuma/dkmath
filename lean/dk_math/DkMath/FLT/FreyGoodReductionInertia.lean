/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyValuationArithmetic
import DkMath.Lib.NumberTheory.EllipticGoodReductionInertia
import DkMath.Lib.RepresentationTheory.LocalFixedCofixed

#print "file: DkMath.FLT.FreyGoodReductionInertia"

/-!
# NOTE-031-002B: Frey曲線の良い素数で実際の残余表現は不分岐

q≠2,pかつq∤abcでは、同じ整数モデルの剰余曲線が非特異である。
pはq上の全ての付値環で単元なので、同じE[p]の全点が慣性に固定される。
モデル・整性・合同・単射性を全て供給し、慣性固定を外部providerに仮定しない。
任意の同じ部分加群Nについて、Fixed側もCofixed側も同時に得られる。

qがabcを割る乗法的還元側は031-002Cへ残す。
この良い素数の定理だけで全素数のhcasesを供給したとはしない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- q≠2,pかつq∤abcで、同じ残余表現の全点を全てのq上の絶対慣性元が固定する。 -/
theorem residual_fixed_at_good_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
    (hσ : σ ∈ inertiaSubgroupIn A ℚ) (P : S.ResidualSpace) :
    S.residualRepresentation σ P = P := by
  have : Fact q.Prime := ⟨hq⟩
  have hg := S.valuation_reduction_isElliptic (Nat.Prime.pos Fact.out) hq2 hd A hA
  have hgood : ((S.valuationModel A).map (IsLocalRing.residue A)).Δ ≠ 0 :=
    isUnit_iff_ne_zero.mp ((WeierstrassCurve.isElliptic_iff _).mp hg)
  have hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    apply valuation_intCast_eq_one_of_not_dvd A hq ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := (p : ℤ))
    intro h
    have hqp' : q ∣ p := by exact_mod_cast h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hqp')
  exact EllipticGoodReductionInertia.fixed_of_inertia_of_good_model S.rationalCurve p A
    (S.valuationModel A) (S.valuationModel_map A) hgood hn σ hσ P

/-- 良い素数では同じ部分加群・商の両方で慣性が自明である。側の二択を選び直さない。 -/
theorem residual_fixed_and_cofixed_at_good_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (N : Submodule (ZMod p) S.ResidualSpace) :
    FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) ∧
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) := by
  constructor
  · intro σ hσ P _
    exact S.residual_fixed_at_good_prime hq hq2 hqp hd A hA σ hσ P
  · intro σ hσ P
    rw [S.residual_fixed_at_good_prime hq hq2 hqp hd A hA σ hσ P, sub_self]
    exact N.zero_mem

end DkMath.FLT.Frey.Source
