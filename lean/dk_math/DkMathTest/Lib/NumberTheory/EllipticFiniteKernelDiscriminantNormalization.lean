/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantNormalization
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDiscriminantNormalization"

namespace DkMathTest.EllipticFiniteKernelDiscriminantNormalization

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticFunctionField
  DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
  DkMath.Lib.NumberTheory.EllipticPointEvaluation
open DkMath.Lib.Algebra
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.NumberTheory.EllipticFiniteKernel

variable {F : Type*} [Field F] [CharZero F] [NeZero (2 : F)]

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q) :
    P ∣ veluHalfNumeratorBase E H :=
  veluX_standard_pair_numerator_dvd E H ho P Q hQ hrel hcop

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q) :
    Q ∣ veluHalfDenominatorBase E H :=
  veluX_standard_pair_denominator_dvd E H ho P Q hQ hrel hcop

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q)
    (hP : P.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hdeg : (veluHalfNumeratorBase E H).natDegree ≤ P.natDegree) :
    P = veluHalfNumeratorBase E H :=
  veluX_standard_pair_numerator_eq_of_monic E H ho P Q hQ hrel hcop hP hA hdeg

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_numerator_dvd
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_denominator_dvd
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_numerator_eq_of_monic

end DkMathTest.EllipticFiniteKernelDiscriminantNormalization
