/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualFiniteLevel
import DkMath.Lib.NumberTheory.EllipticTorsionFinite

#print "file: DkMath.FLT.FreyResidualGeometry"

/-!
# Freyの実際のE[p]の有限性と、位数入力を要しない有限レベル

Sourceが定める同じ有理曲線の幾何学的点群に、標数0の除法多項式のブリッジを適用する。
p≠0なら実際のE[p]は有限となり、既存の開核・有限レベル定理を適用できる。
ここには位数p²の仮定がない。次元2を得るには、引き続き正確な位数公式が必要である。
既約性・Weil対・行列式・慣性群の自明性も、この有限性だけからは結論しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p)

/-- 非零指数での実際の残余空間の有限性。位数公式の仮定を持たない。 -/
theorem residual_finite_of_ne_zero (hp : p ≠ 0) : Finite S.ResidualSpace :=
  finite_torsion_of_ne_zero S.rationalCurve p hp

/-- 素数指数のFrey表現は開核を持つ。有限性は実際の点群から供給する。 -/
theorem residualKernel_isOpen_of_prime [Fact p.Prime] :
    IsOpen (S.residualKernel : Set (Field.absoluteGaloisGroup ℚ)) :=
  S.residualKernel_isOpen

/-- 素数指数の同じFrey表現は、正規な有限中間体の固定部分群で自明となる。 -/
theorem residual_normal_finite_level [Fact p.Prime] :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧ Normal ℚ L ∧ L.fixingSubgroup ≤ S.residualKernel :=
  exists_normal_finite_level S.rationalCurve p

/-- 有限性・位数の追加仮定を持たない、素数指数の有限レベル条件。 -/
theorem residual_factorsThroughFiniteLevel_of_prime [Fact p.Prime] :
    S.ResidualFactorsThroughFiniteLevel := S.residual_factorsThroughFiniteLevel

end DkMath.FLT.Frey.Source
