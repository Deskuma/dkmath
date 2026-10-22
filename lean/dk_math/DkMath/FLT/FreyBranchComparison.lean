/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyShallowSlope
import DkMath.Lib.NumberTheory.EllipticBranchComparison

#print "file: DkMath.FLT.FreyBranchComparison"

/-!
# NOTE-031-002C5: 同じFrey Sourceの枝比較と実際の点の和差

整モデルと一般ファイバーの既存の一致を使い、同じ枝の差・異なる枝の和の滑らかな還元を輸送する。
X差の鋭い深さ評価には、結果が整な有限点であることを明示的に残す。
Sourceの指数・共通因子・向き・曲線を変更しない。浅さと同じ深さは入力であり、
任意のtorsion点の慣性固定を今回の定理だけで結論しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticShallowSlope EllipticGoodReductionSeparation EllipticBranchComparison
open WeierstrassCurve Affine
variable {p : ℕ} (S : Source p) [DecidableEq (AlgebraicClosure ℚ)]

/-- 同じSourceの二点で枝比較を実行し、実際の和差の滑らかな還元と条件付きの鋭い深さを返す。 -/
theorem shallow_sub_of_same_branch (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x₁ y₁) (h₂ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂)
    (hX₁ : A.valuation (x₁ - C.x) < 1) (hX₂ : A.valuation (x₂ - C.x) < 1)
    (hlev : A.valuation (x₁ - C.x) = A.valuation (x₂ - C.x))
    (hsh : A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) < A.valuation (x₁ - C.x) ^ 2)
    (hbr : A.valuation (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) < 1) :
    HasSmoothReduction (S.valuationModel A) (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : AlgebraicClosure ℚ} (h₃ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Point) = Point.some x₃ y₃ h₃ →
          x₃ ∈ A → A.valuation (x₁ - x₂) = A.valuation (x₁ - C.x)) :=
  sub_of_same_branch_of_model (S.valuationModel A) _ (S.valuationModel_map A) C D h₁ h₂ hX₁ hX₂ hlev hsh hbr

/-- 同じSourceの二点で枝比較を実行し、実際の和差の滑らかな還元と条件付きの鋭い深さを返す。 -/
theorem shallow_add_of_opposite_branch (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x₁ y₁) (h₂ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂)
    (hX₁ : A.valuation (x₁ - C.x) < 1) (hX₂ : A.valuation (x₂ - C.x) < 1)
    (hlev : A.valuation (x₁ - C.x) = A.valuation (x₂ - C.x))
    (hsh : A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) < A.valuation (x₁ - C.x) ^ 2)
    (hbr : A.valuation (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) = 1) :
    HasSmoothReduction (S.valuationModel A) (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : AlgebraicClosure ℚ} (h₃ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Point) = Point.some x₃ y₃ h₃ →
          x₃ ∈ A → A.valuation (x₁ - x₂) = A.valuation (x₁ - C.x)) :=
  add_of_opposite_branch_of_model (S.valuationModel A) _ (S.valuationModel_map A) C D h₁ h₂ hX₁ hX₂ hlev hsh hbr

end DkMath.FLT.Frey.Source
