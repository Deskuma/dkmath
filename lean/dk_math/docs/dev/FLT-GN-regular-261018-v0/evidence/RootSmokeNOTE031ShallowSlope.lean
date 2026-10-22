/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath

#print "file: RootSmokeNOTE031ShallowSlope"

/-! 通常入口から分離二根の核・浅い傾きの整性・枝交換・同じSourceへの輸送を確認する。 -/
open DkMath.Lib.NumberTheory EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticShallowSlope

#check DkMath.Lib.Algebra.ValuationSeparatedRoots.branches_of_small_product
#check centreSlope_quadratic
#check slope_mem_and_branches_of_shallow
#check negY_branch_distances
#check opposite_slope_separated_of_shallow
#check DkMath.FLT.Frey.Source.shallow_slope_mem_and_branches
#print axioms DkMath.FLT.Frey.Source.shallow_slope_mem_and_branches

/-- 同じSource 37の同じ中心と方向を保った、浅い有限点の枝分類。 -/
theorem source37_shallow (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))} (D : TangentDirections C)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hnear : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
      A.valuation (x - C.x) ^ 2) :
    centreSlope C x y ∈ A ∧ A.valuation (y - C.y) < 1 ∧
      ((A.valuation (centreSlope C x y - D.α) < 1 ∧ A.valuation (centreSlope C x y - D.β) = 1) ∨
        (A.valuation (centreSlope C x y - D.α) = 1 ∧ A.valuation (centreSlope C x y - D.β) < 1)) :=
  S.shallow_slope_mem_and_branches A D h hnear hsh
