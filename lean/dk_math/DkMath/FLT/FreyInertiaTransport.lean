/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualGeometry
import DkMath.Lib.NumberTheory.EllipticInertiaTransport

#print "file: DkMath.FLT.FreyInertiaTransport"

/-!
# NOTE-031-001: 同じFrey Sourceの局所慣性から大域Fixed/Cofixedへ

Sourceの残余空間・残余表現を変えず、同じ部分加群の全慣性での局所条件を輸送する。
開核は実際のtorsionの有限性から供給済みである。素数性は非零指数を保証する。
一次元性・p≥5・bの偶数性はこの一般的輸送には不要であり、今後の局所算術で扱う。

全素点共通の側を要求する。各素点の独立した二択では足りない。
031-002〜004の局所作用を合流するFreyStableLineLocalGlobalが、本章の入力を算術から供給する。
本章は局所条件を明示する一般形として保持する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 同じSource・同じNが全絶対慣性で点ごとに固定されれば、大域でもFixedとなる。 -/
theorem residual_isFixedOn_of_inertia (N : Submodule (ZMod p) S.ResidualSpace)
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) :
    IsFixedOn S.residualRepresentation N :=
  EllipticTorsionRepresentation.isFixedOn_of_inertia S.rationalCurve p
    (Nat.Prime.ne_zero Fact.out) N hlocal

/-- 同じSourceの商の局所固定を大域Cofixedへ移す。Sourceを選び直さない。 -/
theorem residual_isCofixedOn_of_inertia (N : Submodule (ZMod p) S.ResidualSpace)
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) :
    IsCofixedOn S.residualRepresentation N :=
  EllipticTorsionRepresentation.isCofixedOn_of_inertia S.rationalCurve p
    (Nat.Prime.ne_zero Fact.out) N hlocal

/-- 全局所条件で共通の側を保持した二択を、同じ残余表現の大域二択へ移す。
このhside自体のFrey算術はまだ別入力であり、hcases供給とは区別する。 -/
theorem residual_fixed_or_cofixed_of_inertia_common_side (N : Submodule (ZMod p) S.ResidualSpace)
    (hside :
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q → FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) ∨
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q → CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ))) :
    IsFixedOn S.residualRepresentation N ∨ IsCofixedOn S.residualRepresentation N :=
  EllipticTorsionRepresentation.fixed_or_cofixed_of_inertia_common_side S.rationalCurve p
    (Nat.Prime.ne_zero Fact.out) N hside

end DkMath.FLT.Frey.Source
