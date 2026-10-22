/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyBranchComparison
import DkMath.Lib.NumberTheory.EllipticDoublingDepth

#print "file: DkMath.FLT.FreyDoublingDepth"

/-!
# NOTE-031-002C6a: 同じFrey Sourceの臨界深さと実際の倍点

同じ中心・同じ曲線上の有限点を使い、2倍零点の臨界深さと浅い点の倍点則を輸送する。
Sourceの共通因子・向き・指数は変更しない。2倍零点の深さには2の単元性が必要である。
浅い点の倍点則は任意のtorsion点の浅さを供給する定理ではない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticCriticalDepth EllipticDoublingDepth WeierstrassCurve
variable {p : ℕ} (S : Source p) [DecidableEq (AlgebraicClosure ℚ)]

/-- 同じSourceの有限2倍零点では、2が単元ならX深さの平方がずれの深さに一致する。 -/
theorem two_torsion_critical_depth (A : ValuationSubring (AlgebraicClosure ℚ)) (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1) {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (htor : 2 • Affine.Point.some x y h = 0) (hX : A.valuation (x - C.x) < 1) :
    A.valuation (x - C.x) ^ 2 = A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) :=
  two_torsion_depth C h2 h htor hX

/-- 同じSourceの浅い有限点の実際の2倍を構成し、二つの厳密な場合と相殺閾値の上界を返す。 -/
theorem shallow_doubling_depth (A : ValuationSubring (AlgebraicClosure ℚ)) (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) {x y : AlgebraicClosure ℚ}
    (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y) (hX : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) < A.valuation (x - C.x) ^ 2) :
    ∃ (x₂ y₂ : AlgebraicClosure ℚ) (h₂ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂),
      2 • Affine.Point.some x y h = Affine.Point.some x₂ y₂ h₂ ∧
      A.valuation (x₂ - C.x) * A.valuation (x - C.x) ^ 2 ≤
        max (A.valuation (x - C.x) ^ 4) (A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y)) ∧
      (A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) < A.valuation (x - C.x) ^ 4 →
        A.valuation (x₂ - C.x) = A.valuation (x - C.x) ^ 2) ∧
      (A.valuation (x - C.x) ^ 4 < A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) →
        A.valuation (x₂ - C.x) * A.valuation (x - C.x) ^ 2 = A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y)) :=
  doubling_depth C h hX hsh

end DkMath.FLT.Frey.Source
