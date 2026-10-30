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

#print axioms DkMath.FLT.Frey.Source.residual_kernel_discriminant_product
#print axioms DkMath.FLT.Frey.Source.residual_singular_discriminant_value
#print axioms DkMath.FLT.Frey.Source.residual_smooth_discriminant_value

end DkMathTest.FreyFiniteKernelDiscriminantDepth
