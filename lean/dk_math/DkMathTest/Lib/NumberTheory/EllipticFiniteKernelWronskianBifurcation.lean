/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBifurcation

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelWronskianBifurcation"

namespace DkMathTest.EllipticFiniteKernelWronskianBifurcation

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open DkMath.Lib.NumberTheory.EllipticFunctionField
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly

noncomputable local instance instDecidableEqEllipticFiniteKernelWronskianBifurcationTest
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {F : Type*} [Field F] [CharZero F]

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (c : AlgebraicClosure F) (P : Points E)
    (hPc : ∃ hP : P ∉ H, kernelXAt E H P hP = c) :
    (2 • P ∉ H ∧
      ∃ A B : (AlgebraicClosure F)[X],
        IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree = Nat.card H ∧
          B.natDegree < A.natDegree ∧
          veluX E H =
            aeval (genericX E (AlgebraicClosure F)) A /
              aeval (genericX E (AlgebraicClosure F)) B ∧
          fiberPolynomial A B c ≠ 0 ∧
          (normalize (fiberPolynomial A B c)).Monic ∧
          (normalize (fiberPolynomial A B c)).natDegree = Nat.card H ∧
          normalize (fiberPolynomial A B c) =
            ∏ Q : H, (Polynomial.X - Polynomial.C ((P + Q.val).xc))) ∨
    (2 • P ∈ H ∧
      ∃ T : Points E, T ∉ H ∧ -T = T ∧
        ∃ hT : T ∉ H, kernelXAt E H T hT = c ∧
          ∃ A B : (AlgebraicClosure F)[X],
            IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree = Nat.card H ∧
              B.natDegree < A.natDegree ∧
              veluX E H =
                aeval (genericX E (AlgebraicClosure F)) A /
                  aeval (genericX E (AlgebraicClosure F)) B ∧
              fiberPolynomial A B c ≠ 0 ∧
              (normalize (fiberPolynomial A B c)).Monic ∧
              (normalize (fiberPolynomial A B c)).natDegree = Nat.card H ∧
              (∀ (R : Points E) (hR : R ∉ H),
                kernelXAt E H R hR = c →
                  (normalize (fiberPolynomial A B c)).IsRoot R.xc) ∧
              normalize (fiberPolynomial A B c) =
                fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
                  (fun Q : halfKernel E H => (T + Q.val.val).xc)) :=
  exists_veluX_normalized_fiberFactor_or_fullKernel E H ho c P hPc

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.exists_veluX_normalized_fiberFactor_or_fullKernel

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    ∃ A B : (AlgebraicClosure F)[X],
      IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree = Nat.card H ∧
        B.natDegree < A.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure F)) A /
          aeval (genericX E (AlgebraicClosure F)) B ∧
        ∀ (c : AlgebraicClosure F) (P : Points E) (hP : P ∉ H),
          kernelXAt E H P hP = c → fixedPairFiberBranch E H A B c P hP := by
  exact exists_veluX_fixed_pair_factorization E H ho

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    ∃ A B : (AlgebraicClosure F)[X],
      IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree = Nat.card H ∧
        B.natDegree < A.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure F)) A /
          aeval (genericX E (AlgebraicClosure F)) B ∧
        ∀ c : AlgebraicClosure F, ∃ (P : Points E) (hP : P ∉ H),
          kernelXAt E H P hP = c ∧ fixedPairFiberBranch E H A B c P hP := by
  exact exists_veluX_fixed_pair_factorization_all_fibers E H ho

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.fixedPairFiberBranch_of_veluX_quotient
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.exists_veluX_fixed_pair_factorization
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.exists_veluX_fixed_pair_factorization_all_fibers

example (A B : (AlgebraicClosure F)[X]) (c : AlgebraicClosure F)
    (hdeg : B.natDegree < A.natDegree) :
    (fiberPolynomial A B c).leadingCoeff = A.leadingCoeff :=
  fiberPolynomial_leadingCoeff_eq_of_natDegree_lt hdeg

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.fiberPolynomial_leadingCoeff_eq_of_natDegree_lt

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H) :
    (halfKernel E H).Nonempty :=
  halfKernel_nonempty_of_one_lt_card E H ho hcard

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.halfKernel_nonempty_of_one_lt_card

example (A B : (AlgebraicClosure F)[X]) (c : AlgebraicClosure F)
    (hdeg : 0 < (fiberPolynomial A B c).degree)
    (hdiv : (Polynomial.X - Polynomial.C (1 : AlgebraicClosure F)) ^ 2 ∣
      normalize (fiberPolynomial A B c)) :
    (fiberPolynomial A B c).discr = 0 := by
  apply discr_eq_zero_of_sq_dvd_normalize hdeg hdiv
  exact not_isUnit_of_degree_pos _ (by rw [degree_X_sub_C]; norm_num)

#print axioms DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly.discr_eq_zero_of_sq_dvd_normalize

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (A B : (AlgebraicClosure F)[X])
    (hFdeg : A.natDegree = Nat.card H) (hGlt : B.natDegree < A.natDegree)
    (c : AlgebraicClosure F) (P : Points E) (hP : P ∉ H)
    (hbranch : fixedPairFiberBranch E H A B c P hP)
    (htwo : 2 • P ∈ H) :
    (fiberPolynomial A B c).discr = 0 :=
  fixedPairFiberBranch_discr_eq_zero_of_two_smul_mem E H ho hcard A B
    hFdeg hGlt c P hP hbranch htwo

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.fixedPairFiberBranch_discr_eq_zero_of_two_smul_mem

example (A : (AlgebraicClosure F)[X]) (hsep : A.Separable)
    (hdeg : 0 < A.degree) : A.discr ≠ 0 :=
  discr_ne_zero_of_separable hdeg hsep

#print axioms DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly.discr_ne_zero_of_separable

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (A B : (AlgebraicClosure F)[X])
    (hFdeg : A.natDegree = Nat.card H) (hGlt : B.natDegree < A.natDegree)
    (c : AlgebraicClosure F) (P : Points E) (hP : P ∉ H)
    (hbranch : fixedPairFiberBranch E H A B c P hP)
    (htwo : 2 • P ∉ H) :
    (fiberPolynomial A B c).discr ≠ 0 :=
  fixedPairFiberBranch_discr_ne_zero_of_two_smul_not_mem E H ho A B
    hFdeg hGlt c P hP hbranch htwo

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.fixedPairFiberBranch_discr_ne_zero_of_two_smul_not_mem

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (A B : (AlgebraicClosure F)[X])
    (hFdeg : A.natDegree = Nat.card H) (hGlt : B.natDegree < A.natDegree)
    (c : AlgebraicClosure F) (P : Points E) (hP : P ∉ H)
    (hbranch : fixedPairFiberBranch E H A B c P hP) :
    (fiberPolynomial A B c).discr = 0 ↔ 2 • P ∈ H :=
  fixedPairFiberBranch_discr_eq_zero_iff_two_smul_mem E H ho hcard A B
    hFdeg hGlt c P hP hbranch

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.fixedPairFiberBranch_discr_eq_zero_iff_two_smul_mem

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H) :
    ∃ A B : (AlgebraicClosure F)[X],
      IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree = Nat.card H ∧
        B.natDegree < A.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure F)) A /
          aeval (genericX E (AlgebraicClosure F)) B ∧
        ∀ c : AlgebraicClosure F, ∃ (P : Points E) (hP : P ∉ H),
          kernelXAt E H P hP = c ∧
            ((fiberPolynomial A B c).discr = 0 ↔ 2 • P ∈ H) :=
  exists_veluX_fixed_pair_discriminant_branch_iff E H ho hcard

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.exists_veluX_fixed_pair_discriminant_branch_iff

end DkMathTest.EllipticFiniteKernelWronskianBifurcation
