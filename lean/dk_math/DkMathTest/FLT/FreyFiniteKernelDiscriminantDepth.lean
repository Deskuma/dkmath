/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyFiniteKernelDiscriminantDepth

#print "file: DkMathTest.FLT.FreyFiniteKernelDiscriminantDepth"

namespace DkMathTest.FreyFiniteKernelDiscriminantDepth

open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.ValuationInertia
open DkMath.FLT.Frey.Source
open WeierstrassCurve

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 教科書回帰例：Frey Source の残余核を一般 hprod へ特殊化する。 -/
example (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1) :
    letI := S.finite_residualPointSubgroup L hl
    letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
    (S.residualKernelModel L hl).Δ *
        (∏ Q : halfKernel S.rationalCurve (pointSubgroup S.rationalCurve p L),
          (2 * Q.val.val.yc +
            (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * Q.val.val.xc +
            (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 4 =
      (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ p :=
  residual_kernel_discriminant_product S hp2 L hl

/-- 教科書回帰例：整数標的と代数閉包上の商標的の局所判別式を比較する。 -/
example (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A q) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) =
      A.valuation (S.residualKernelModel L hl).Δ :=
  residual_integer_kernel_discriminant_value_eq S hp2 L hl hs hq hqp A hA

/-- 教科書回帰例：2上の特異枝をFreyの`-8 mod p`算術で排除する。 -/
example (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) :
    ¬ Disjoint L (S.residualZeroComponent A) :=
  residual_disjoint_kernel_impossible_at_two S hp5 L hl hs A hA

/-- 教科書回帰例：二分法と特異枝排除から2上の零成分包含を得る。 -/
example (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) :
    L ≤ S.residualZeroComponent A :=
  residual_stable_line_le_zeroComponent_at_two S hp5 L hl hs A hA

/-- 教科書回帰例：2上の安定一次元核を零成分そのものへ同定する。 -/
example (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) :
    L = S.residualZeroComponent A :=
  residual_stable_line_eq_zeroComponent_at_two S hp5 L hl hs A hA

#print axioms DkMath.FLT.Frey.Source.residual_kernel_discriminant_product
#print axioms DkMath.FLT.Frey.Source.residual_singular_discriminant_value
#print axioms DkMath.FLT.Frey.Source.residual_smooth_discriminant_value
#print axioms DkMath.FLT.Frey.Source.residual_integer_kernel_discriminant_value_eq
#print axioms DkMath.FLT.Frey.Source.residual_integer_singular_discriminant_value
#print axioms DkMath.FLT.Frey.Source.residual_integer_smooth_discriminant_value
#print axioms DkMath.FLT.Frey.Source.residual_disjoint_kernel_impossible_at_two
#print axioms DkMath.FLT.Frey.Source.residual_stable_line_le_zeroComponent_at_two
#print axioms DkMath.FLT.Frey.Source.residual_stable_line_eq_zeroComponent_at_two

end DkMathTest.FreyFiniteKernelDiscriminantDepth
