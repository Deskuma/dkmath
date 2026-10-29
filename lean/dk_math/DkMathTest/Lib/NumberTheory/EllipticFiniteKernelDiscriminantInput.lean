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
open Polynomial

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

example (a : AlgebraicClosure F) :
    (xCorrectionDenominator a).Monic :=
  xCorrectionDenominator_monic a

example (a : AlgebraicClosure F) :
    (xCorrectionDenominator a).natDegree = 2 :=
  xCorrectionDenominator_natDegree a

example (W : WeierstrassCurve (AlgebraicClosure F)) (a b : AlgebraicClosure F) :
    (xCorrectionNumerator W a b).natDegree ≤ 1 :=
  xCorrectionNumerator_natDegree_le_one W a b

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H] :
    (veluHalfDenominatorBase E H).Monic :=
  veluHalfDenominatorBase_monic E H

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H] :
    (veluHalfDenominatorBase E H).natDegree = 2 * (halfKernel E H).card :=
  veluHalfDenominatorBase_natDegree E H

example {F₀ G₀ A₀ D₀ : (AlgebraicClosure F)[X]}
    (hcop : IsCoprime F₀ G₀) (hcross : F₀ * D₀ = A₀ * G₀) : F₀ ∣ A₀ :=
  dvd_of_cross_relation_of_coprime hcop hcross

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_eval_eq_root_distance_product_sq
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_eval_eq_root_product_sq
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.xCorrectionDenominator_monic
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.xCorrectionDenominator_natDegree
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.xCorrectionNumerator_natDegree_le_one
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_monic
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_natDegree
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.dvd_of_cross_relation_of_coprime

end DkMathTest.EllipticFiniteKernelDiscriminantInput
