/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantInput

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDiscriminantInput"

namespace DkMathTest.EllipticFiniteKernelDiscriminantInput

open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

variable {F : Type*} [Field F] [CharZero F]

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H]
    (e : AlgebraicClosure F) :
    (veluHalfDenominatorBase E H).eval e =
      ∏ Q ∈ halfKernel E H, (e - Q.val.xc) ^ 2 :=
  veluHalfDenominatorBase_eval_eq_root_distance_product_sq E H e

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H]
    (e : AlgebraicClosure F) :
    (veluHalfDenominatorBase E H).eval e =
      ∏ Q ∈ halfKernel E H, (Q.val.xc - e) ^ 2 :=
  veluHalfDenominatorBase_eval_eq_root_product_sq E H e

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_eval_eq_root_distance_product_sq
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_eval_eq_root_product_sq

end DkMathTest.EllipticFiniteKernelDiscriminantInput
