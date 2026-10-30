/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantProduct

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDiscriminantProduct"

namespace DkMathTest.EllipticFiniteKernelDiscriminantProduct

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- 教科書回帰例：奇数有限核の三つの2捩れ枝を組み合わせた判別式積を再利用する。 -/
example (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    (kernelModel E H).Δ *
        (∏ Q : halfKernel E H,
          (2 * Q.val.val.yc +
            (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
            (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2) ^ 4 =
      (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ Nat.card H :=
  kernelModel_discriminant_product_of_odd_card E H ho

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.kernelModel_discriminant_product_of_odd_card

end DkMathTest.EllipticFiniteKernelDiscriminantProduct
