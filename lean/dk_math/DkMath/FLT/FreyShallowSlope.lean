/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNodalReduction
import DkMath.Lib.NumberTheory.EllipticShallowSlope

#print "file: DkMath.FLT.FreyShallowSlope"

/-!
# NOTE-031-002C4: 同じFrey有限点の浅い中心傾きと二方向

C3が構成した同じC,Dを使い、実際の曲線方程式と浅さから傾きの整性と枝を供給する。
近さ・浅さは明示的な入力であり、全てのtorsion点に成立すると仮定しない。
負号による点の反転は方向を交換する。各方向の慣性固定から点自体の固定を導く段階はまだ残る。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticShallowSlope
variable {p : ℕ} (S : Source p)

/-- 同じSourceの同じ有限点で、近さ・浅さから傾きの整性と排他的な枝を得る。
素数性やq≠pはこの幾何学の輸送には不要で、torsion仮定も加えない。 -/
theorem shallow_slope_mem_and_branches (A : ValuationSubring (AlgebraicClosure ℚ))
    {C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))} (D : TangentDirections C)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hnear : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
      A.valuation (x - C.x) ^ 2) :
    centreSlope C x y ∈ A ∧ A.valuation (y - C.y) < 1 ∧
      ((A.valuation (centreSlope C x y - D.α) < 1 ∧ A.valuation (centreSlope C x y - D.β) = 1) ∨
        (A.valuation (centreSlope C x y - D.α) = 1 ∧ A.valuation (centreSlope C x y - D.β) < 1)) :=
  slope_mem_and_branches_of_shallow D h.1 hnear hsh

/-- 同じSourceの浅い点と負号の点は、中心傾きが単元の差で分離される。
負号の座標を元の同じ曲線で計算し、別のモデルや中心へ置き換えない。 -/
theorem shallow_opposite_slope_separated (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hnear : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
      A.valuation (x - C.x) ^ 2) :
    A.valuation (centreSlope C x y - centreSlope C x
      ((S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.negY x y)) = 1 :=
  opposite_slope_separated_of_shallow C h.1 hnear hsh

end DkMath.FLT.Frey.Source
