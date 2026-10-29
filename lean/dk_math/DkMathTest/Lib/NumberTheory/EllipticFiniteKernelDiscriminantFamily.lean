/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantFamily

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDiscriminantFamily"

namespace DkMathTest.EllipticFiniteKernelDiscriminantFamily

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.Algebra.RationalPolynomialDiscriminant
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open DkMath.Lib.NumberTheory.EllipticFunctionField
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

noncomputable local instance instDecidableEqEllipticFiniteKernelDiscriminantFamilyTest
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {F : Type*} [Field F] [CharZero F]

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H) :
    ∃ A B : (AlgebraicClosure F)[X],
      IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree = Nat.card H ∧
        B.natDegree < A.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure F)) A /
          aeval (genericX E (AlgebraicClosure F)) B ∧
        ∀ (c : AlgebraicClosure F) (P : Points E) (hP : P ∉ H),
          kernelXAt E H P hP = c →
            ((fiberDiscriminantFamily A B).eval c = 0 ↔ 2 • P ∈ H) :=
  exists_veluX_fixed_pair_discriminant_family_branch_iff_all_points E H ho hcard

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H) :
    ∃ A B : (AlgebraicClosure F)[X],
      IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree = Nat.card H ∧
        B.natDegree < A.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure F)) A /
          aeval (genericX E (AlgebraicClosure F)) B ∧
        ∀ c : AlgebraicClosure F,
          (fiberDiscriminantFamily A B).eval c = 0 ↔
            ∃ P : Points E, ∃ hP : P ∉ H,
              kernelXAt E H P hP = c ∧ 2 • P ∈ H :=
  exists_veluX_fixed_pair_discriminant_family_zero_iff_two_torsion_image
    E H ho hcard

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.exists_veluX_fixed_pair_discriminant_family_branch_iff_all_points
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.exists_veluX_fixed_pair_discriminant_family_zero_iff_two_torsion_image

end DkMathTest.EllipticFiniteKernelDiscriminantFamily
