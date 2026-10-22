/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation
import DkMath.Lib.NumberTheory.EllipticTorsionFinite

#print "file: DkMath.Lib.NumberTheory.EllipticInertiaTransport"

/-!
# NOTE-031-001: 実際の有理曲線のtorsion表現への輸送

非零nでは、除法多項式により実際のE[n]が有限であり、同じ座標作用の核が開く。
これを絶対慣性の局所大域定理へ供給する。開核や慣性の持ち上げを別のproviderに取らない。
残る入力は全素数・全付値環での同じ部分加群の局所Fixedまたは局所Cofixedである。
ここでは還元理論からその局所入力自体を証明したとはしない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open ValuationInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable (E : WeierstrassCurve ℚ) (n : ℕ)

/-- 非零nの同じ実際のE[n]で、全絶対慣性によるNの固定を大域Fixedへ移す。 -/
theorem isFixedOn_of_inertia (hn : n ≠ 0) (N : Submodule (ZMod n) (Torsion E n))
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → FixedOn (representation E n) N (inertiaSubgroupIn A ℚ)) :
    IsFixedOn (representation E n) N :=
  AbsoluteInertiaRepresentation.isFixedOn_of_inertia (representation E n) N
    (representationKernel_isOpen_of_ne_zero E n hn) hlocal

/-- 同じE[n]・同じNの商の局所固定を大域Cofixedへ移す。安定性の追加入力は不要である。 -/
theorem isCofixedOn_of_inertia (hn : n ≠ 0) (N : Submodule (ZMod n) (Torsion E n))
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → CofixedOn (representation E n) N (inertiaSubgroupIn A ℚ)) :
    IsCofixedOn (representation E n) N :=
  AbsoluteInertiaRepresentation.isCofixedOn_of_inertia (representation E n) N
    (representationKernel_isOpen_of_ne_zero E n hn) hlocal

/-- 全素点で共通の側を選んだ場合に限り、実際のE[n]の大域二択へ接続する。 -/
theorem fixed_or_cofixed_of_inertia_common_side (hn : n ≠ 0)
    (N : Submodule (ZMod n) (Torsion E n))
    (hside :
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q → FixedOn (representation E n) N (inertiaSubgroupIn A ℚ)) ∨
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q → CofixedOn (representation E n) N (inertiaSubgroupIn A ℚ))) :
    IsFixedOn (representation E n) N ∨ IsCofixedOn (representation E n) N :=
  AbsoluteInertiaRepresentation.fixed_or_cofixed_of_inertia_common_side (representation E n) N
    (representationKernel_isOpen_of_ne_zero E n hn) hside

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
