/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticLocalComponentObstruction

#print "file: DkMathTest.Lib.NumberTheory.EllipticLocalComponentObstruction"

/-!
# 教科書回帰例：有限剰余体の局所成分障害

`localValuationSubring q` を明示的に選ぶことで、抽象的な有限剰余体仮定を
実際の `q`-進住所へ特殊化する。ここでは定理の型を再利用するだけに留め、
特異中心や位数 `2*p` 点の存在を別途構成したとは主張しない。
-/

namespace DkMathTest.Lib.NumberTheory.EllipticLocalComponentObstruction

open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.FreyLocalReduction
open DkMath.Lib.NumberTheory.EllipticLocalComponentObstruction
open DkMath.Lib.NumberTheory.EllipticNodalSmoothCard
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open IsLocalRing

noncomputable section

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

example (hqp : q ≠ p) :
    (localValuationSubring q).valuation (p : ℚ) = 1 :=
  localValuationSubring_prime_valuation_eq_one hqp

example (hp5 : 5 ≤ p) (hqp : q ≠ p) (hqp' : q < p)
    (W : WeierstrassCurve (localValuationSubring q))
    (C : SingularCentre (W.map (IsLocalRing.residue (localValuationSubring q))))
    {R : (W.map (localValuationSubring q).subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction W R ∧
      p ∣ Nat.card ((W.map (localValuationSubring q).subtype).toAffine.Point ⧸
        zeroComponentSubgroup W) :=
  localValuationSubring_component_prime_dvd_of_singularCentre
    hp5 hqp hqp' W C hR

#print axioms localValuationSubring_prime_valuation_eq_one
#print axioms localValuationSubring_component_prime_dvd_of_singularCentre

end
end DkMathTest.Lib.NumberTheory.EllipticLocalComponentObstruction
